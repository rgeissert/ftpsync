#! /usr/bin/perl -w

# this copy forked off the original fork by Joy
# just to get the two archive thingies monitored, quick'n'dirty
# 2007-10-14

# Copyright (C) 2001-2002 Adam Lackorzynski
#
# This file contains free software, you can redistribute it and/or modify 
# it under the terms of the GNU General Public License, Version 2 as 
# published by the Free Software Foundation (see the file COPYING). 
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# Adam Lackorzynski <adam@os.inf.tu-dresden.de>

# todo
# - time of query (maybe, will consume too much space)
# - maybe some bars marking time all the servers are behind the
#   the most recent server
# - rewrite and do it better this time...

use strict;
use LWP::UserAgent;
use Data::Dumper;
use Getopt::Long;
use File::Listing;
use Carp ();

#local $SIG{__WARN__} = \&Carp::confess; #cluck;
#local $SIG{__DIE__}  = \&Carp::confess;
#$SIG{INT} = \&Carp::confess;

my $hostpattern =
#'([wp]\.de\.debian\.org$|den\.de$|erlangen|(se|uk|fi)\.debian)';
#'(\.debian\.org$|\.de$)';
#'([pw]\.de\.debian\.|dresden|claus)';
#'dresden';
#'(claus)';
#'((www|ftp).de.debian.org$)';
#'www\..+\.debian.org';
#'(\.de$)';
#'(ftp|www)\.(se|de|at|es|fr|uk|it|pl|nl|tr).debian.org$|\.de$';
#'ftp.wa.au';
#'www.mirror.ac.uk|dresden|claus|\.de.debian.org|erlan|berlin';
#'www.mirror.ac.uk';
#'www2';
#'ftp.(at|si).debian.org';
#'ftp.si.debian.org';
'.';
#'.debian.org';

my $tracedir_std_main   = "project/trace";
my $masterfile_stdmain  = "ftp-master.debian.org";
my $tracedir_std_cd     = "project/trace";
my $masterfile_stdcd    = "cdimage.debian.org";
my $tracedir_std_www    = "mirror/timestamps";
my $masterfile_stdwww   = "www-master.debian.org";

my $tracedir_std_old    = "project/trace";
my $masterfile_stdold   = "saens.debian.org"; # FIXME :)
my $tracedir_std_nonus  = "project/trace";
my $masterfile_stdnonus = "non-us.debian.org";

my $archivUpdatePattern = "Archive-Update-in-Progress-";

my $masterlistURL = 'http://cvs.debian.org/*checkout*/webwml/english/mirror/Mirrors.masterlist?cvsroot=webwml';

my @sections   = qw/old nonus/;

# order of protocols is important -> ftp is easier to parse for the upstream
# mirror list, so do this one first...
my %protocols =
  (
    old   => [qw/ftp http rsync/],
    nonus => [qw/ftp http rsync/],
  );

my %addrs =
  (
#   'debian.inf.tu-dresden.de' =>
#   {
#    main => 
#    { path  => '/debian',
#      tracedir => $tracedir_std_main,   mastertracefile  => $masterfile_stdmain, },
#    cd =>
#    { path_http => '/debian-cd', path_ftp => '/debian-cd', patch_rsync => 'debian-cd', },
#   },
#   'os.inf.tu-dresden.de' =>
#   {
#    main => 
#    { path  => '/debian',
#      tracedir => $tracedir_std_main,   mastertracefile  => $masterfile_stdmain, },
#    checkProtocol => [ 'http', ],
#    cd =>
#    { path_http => '/debian-cd'},
#   },
 );

my $debug = 1;
my $DisplayNonCheckedHosts = 0;

my $HtmlDir    = "../www/archive";
my $HtmlFile   = "status.html";
my $MasterFile = "master.list";
my $DataFile   = "mirror.data";
my $DataFileIP = "mirror.data.ip";

my @arg_options = ("masterfile|m=s", \$MasterFile,
                   "datafile|d=s", \$DataFile,
		   "datafileip|i=s", \$DataFileIP,
		   "htmlfile|o=s", \$HtmlFile,
		   "displaynonchecked!", \$DisplayNonCheckedHosts,
                  );

# some mirrors have authenticated rsync access only although they're in
# the mirror list...
# do not let rsync pop up with a password prompt
$ENV{'RSYNC_PASSWORD'} = '';

umask 022;
my $MasterListRefreshTime = 24*3600;   # 1 day
my $IPListRefreshTime     = 2*24*2600; # 2 days
my $OutOfDateTime         = 3600*24*2; # 2 days
my $connectionTimeout = 10; # secs
my $prog_rsync = "rsync --timeout=$connectionTimeout";
my %timestamps =
 (
    data_capture_start => 0,
    data_capture_end   => 0,
 );
my $IPDataCaptureTime = 0;

my $ERRORMSGCUTBYTES = 200;

my %data;
my %IPs;
my (@errors_full, @errors_filt);
my %openedfile = ();

sub DBG {
  print join("", @_) if $debug;
}

sub getTempFile {
  $_ = `/bin/mktemp /tmp/mirstat.temp.XXXXXX`;
  chomp;
  $_;
}

sub getHtmlFullErrorFileName {
  my $r;
  if ($HtmlFile =~ /\.html$/) {
    ($r = $HtmlFile) =~ s/html$/full-errors.$&/i;
  } else {
    $r = $HtmlFile."full-errors.html";
  }
  $r;
}

sub rsyncErrorFilter {
  my ($text) = @_;
  # In rsync error messages normally only the last line is significant
  (reverse split(/\n/, $text))[0];
}

sub getErrorNrFull {
  my ($text) = @_;
  my $i = 0;
  for (; $i <= $#errors_full; $i++) {
    return $i if ($errors_full[$i] eq $text);
  }
  $errors_full[$i] = $text;
  $i;
}

sub getErrorNr {
  my ($text, $protocol) = @_;
  my $i = getErrorNrFull($text);
  if ($protocol =~ /rsync/) {
     $text = rsyncErrorFilter($text);
  }
  # trim text also in case it's too long
  $errors_filt[$i] = substr($text, 0, $ERRORMSGCUTBYTES);
  $i;
}

sub parseMasterData {
  my ($host, $key, $val) = @_;

  # print "$host $key $val\n";
  $val =~ s,(.)/$,$1,;

  if ($key =~ /Archive-/) {
    $addrs{$host}{main}{mastertracefile}  = $masterfile_stdmain;
    $addrs{$host}{main}{tracedir}   = $tracedir_std_main;
  } elsif ($key =~ /CDImage-/) {
    $addrs{$host}{cd}{mastertracefile} = $masterfile_stdcd;
    $addrs{$host}{cd}{tracedir}  = $tracedir_std_cd;
  } elsif ($key =~ /WWW-/) {
    $addrs{$host}{www}{mastertracefile}   = $masterfile_stdwww;
    $addrs{$host}{www}{tracedir}    = $tracedir_std_www;
  } elsif ($key =~ /Old-/) {
    $addrs{$host}{old}{mastertracefile}   = $masterfile_stdold;
    $addrs{$host}{old}{tracedir}    = $tracedir_std_old;
  } elsif ($key =~ /NonUS-/) {
    $addrs{$host}{nonus}{mastertracefile}   = $masterfile_stdnonus;
    $addrs{$host}{nonus}{tracedir}    = $tracedir_std_nonus;
  }

  if ($key =~ /Archive-http/i) {
    $addrs{$host}{main}{path_http} = $val;
  } elsif ($key =~ /Archive-ftp/i) {
    $addrs{$host}{main}{path_ftp}  = $val;
  } elsif ($key =~ /Archive-rsync/i) {
    $addrs{$host}{main}{path_rsync} = $val;
  } elsif ($key =~ /CDImage-http/i) {
    $addrs{$host}{cd}{path_http} = $val;
  } elsif ($key =~ /CDImage-ftp/i) {
    $addrs{$host}{cd}{path_ftp}  = $val;
  } elsif ($key =~ /CDImage-rsync/i) {
    $addrs{$host}{cd}{path_rsync} = $val;
  } elsif ($key =~ /WWW-http/i) {
    $addrs{$host}{www}{path_http} = $val;
  } elsif ($key =~ /Old-http/i) {
    $addrs{$host}{old}{path_http} = $val;
  } elsif ($key =~ /Old-ftp/i) {
    $addrs{$host}{old}{path_ftp}  = $val;
  } elsif ($key =~ /Old-rsync/i) {
    $addrs{$host}{old}{path_rsync} = $val;
  } elsif ($key =~ /NonUS-http/i) {
    $addrs{$host}{nonus}{path_http} = $val;
  } elsif ($key =~ /NonUS-ftp/i) {
    $addrs{$host}{nonus}{path_ftp}  = $val;
  } elsif ($key =~ /NonUS-rsync/i) {
    $addrs{$host}{nonus}{path_rsync} = $val;
  }
  # save all other info
  $addrs{$host}{info}{$key} = $val;
}

sub parseMirrorsMasterList {
  my $ctime = 0;
  $ctime = (stat($MasterFile))[9] if -f $MasterFile;
  if ($ctime + $MasterListRefreshTime < time) {
    DBG("Getting new master mirror list\n");
    open(F, "wget -q -O - '$masterlistURL' | tee $MasterFile |") or die $!;
  } else {
    open(F, $MasterFile) or die $!;
  }
  my $s = 0;
  my ($host, $entryval, $entrykey) = (undef, undef, undef);
  while (defined ($_=<F>)) {
    chomp;
    s/\s*$//;
    if ($s == 0) { # looking for site
      next if /^$/;
      next if /^X-/;
      next if /^\s\S/;
      die "format error ($_)" unless /^Site:\s*(\S+)/;
      $host = $1;
      $s = 1;
    } else {
      if (/^$/) {  # end of description
        $s = 0;
	parseMasterData($host, $entrykey, $entryval)
	  if (defined $entrykey);
	$entrykey = undef;
      } else {
        if (/^\s+/) {  # continued line (starting with \s's)
          s/^\s*/ /;
	  $entryval .= $_;
	} else {
	  parseMasterData($host, $entrykey, $entryval) 
	    if (defined $entrykey);

          ($entrykey, $entryval) = split(/: */, $_, 2);
	  die "format error($_)" unless $entrykey && $entryval;
	}
      }
    }
  }
  close F;
}

sub getSecondsOfDatestring {
  my ($datestring) = @_;
  $datestring = (split(/\n/, $datestring))[0];
  $_ = `date -d "$datestring" +%s 2>&1`;
  chomp;
  return "ERROR: $_" if $?;
  $_;
}

# get output from http/ftp request
sub getData_ftp_http {
  my ($url) = @_;
  my $ua = LWP::UserAgent->new;
  $ua->agent(" ");
  $ua->timeout($connectionTimeout);
  my $res = $ua->request(HTTP::Request->new(GET => $url));
  return 'ERROR: ' . $res->status_line if $res->is_error;
  my $d = $res->content;
  chomp $d;
  return $d;
}

# get file via rsync
sub getData_rsync_file {
  my ($url) = @_;
  my $tmpf = getTempFile();
  my $d = `$prog_rsync $url $tmpf 2>&1`;

  # check for error messages - yes, can return with $?==0 although
  # we've got an error (@ERROR: access denied...)
  if ($d =~ /^\@ERROR: /m) {
    $d = 'ERROR: '.$d;
  } elsif (!$?) {
    # request succesful
    $d = '';
    open(D, $tmpf) || die $!;
    while (defined ($_=<D>)) {
      chomp;
      $d .= $_;
    }
    close D;
  } # fall through otherwise...

  unlink $tmpf;
  $d;
}

# get output from rsync request
sub getData_rsync_output {
  my ($url) = @_;
  my $d = `$prog_rsync '$url' 2>&1`;
  $d = 'ERROR: '.$d if $?;
  $d;
}

sub getFile {
  my ($url) = @_;
  if ($url =~ /^(ht|f)tp:/) {
    return getData_ftp_http($url);
  } elsif ($url =~ /^rsync:/) {
    return getData_rsync_file($url);
  } else {
    die "INTERNAL ERROR: unknown protocol type!";
  }
}

sub getDirListing {
  my ($url) = @_;
  if ($url =~ /^rsync:/) {
    $url .= '/*' if ($url =~ /[^*]$/);
    return getData_rsync_output($url);
  } else {
    $url .= '/' if $url !~ /\/$/;
    return getData_ftp_http($url);
  }
}

sub removeHTMLTags {
  $_ = shift;
  s/<.*?>//sg;
  $_;
}

sub getPathForProtocol {
  my ($host, $section, $protocol) = @_;
  my $path = (defined $addrs{$host}{$section}{"path_$protocol"})?
              $addrs{$host}{$section}{"path_$protocol"}:
	      $addrs{$host}{$section}{path};
  $path = '/'.$path if (defined $path && $path !~ m,^/,); 	   
  $path;
}

sub checkUpdateInProgress {
  my ($section) = @_;
  ($section eq 'www')?0:1;
}

sub checkIfUpdateIsInProgress {
  my ($protocol, $host, $path, $section) = @_;

  # we check if an archiv update is in progress
  # (by simply getting the directory listing of the topmost dir)
  my $r = getDirListing("$protocol://$host$path");
  DBG($r, "\n");
  $data{$host}{$section}{updateInProgess} =
    ($r =~ /$archivUpdatePattern/im)?1:0;
  $data{$host}{$section}{$protocol} =
    ($r !~ /^ERROR: /m)?-1:getErrorNr($r, $protocol);
}

sub extractFileLinksFromDirHTMLListing {
  my ($listing) = @_;

  my @files;
  while ($listing =~ s/href\s*=\s*"?(.*?)[^\/\w.\d-](.*)/$2/i) {
    my $a = $1;
    #$a = (reverse split(/\//, $a))[0] if $a =~ /\//;
    next if $a =~ m,/,; # don't take directories
    next if (!defined $a || $a eq '' || $a =~ /^(http|ftp|mailto|trace)$/i);
    if ($a !~ /\/$/) {
      push @files, $a
        if ($a !~ /^\.$/ && $a !~ /^\.\.$/ && $a !~ /^\./ && $a !~ /\.$/);
    }
  }
  @files;
}

sub extractFileLinksFromDirRsyncListing {
  my ($listing) = @_;
  my @files;

  for my $l (split(/\n/, $listing)) {
    next unless ($l =~ /^.[rwxsSXt-]{9}\s/);
    (my $name = $l) =~ s/.*\s([^\s]+)$/$1/;
    push @files, $name;
  }

  @files;
}

sub extractFileLinksFromDirFTPListing {
  my ($listing) = @_;
  my @files;

  for (parse_dir($listing)) {
    my ($name) = @$_;
    push @files, $name;
  }
  @files;
}

sub getLinkFilesOutOfListing {
  my ($protocol, $listing) = @_;
  my @files;
  if ($protocol eq 'rsync') {
    return extractFileLinksFromDirRsyncListing($listing);
  } elsif ($protocol eq 'http') {
    return extractFileLinksFromDirHTMLListing($listing);
  } elsif ($protocol eq 'ftp') {
    return extractFileLinksFromDirFTPListing($listing);
  } else {
    print STDERR "not impl\n";
  }
  return ();
}

sub cleanOutNonMirrorTraceFiles {
  my (@list) = @_;

  my @nl;
  for (@list) {
    next if (/\.(html?|css)$/);
    push @nl, $_;
  }
  @nl;
}

sub uniqueList {
  my (@list) = @_;

  my @nl;
  my $d = '';
  for (sort @list) {
    push @nl, $_ if $d ne $_;
    $d = $_;
  }
  @nl;
}

sub masterSet__ {
  my ($t, $failret, $host, $section, $val) = @_;
  return $failret unless defined $addrs{$host}{$section}{mastertracefile};
  $data{$host}{$section}{$t}{$addrs{$host}{$section}{mastertracefile}}
    = $val if defined $val;
  $data{$host}{$section}{$t}{$addrs{$host}{$section}{mastertracefile}};
}
sub masterTimeString { return masterSet__('timestamps_str', '', @_); }
sub masterSeconds    { return masterSet__('timestamps_sec',  0, @_); }

sub getUndefinedTimestampFile {
  my ($host, $section) = @_;
  foreach my $m (keys %{$data{$host}{$section}{timestamps_str}}) {
    return $m unless defined $data{$host}{$section}{timestamps_str}{$m};
  }
  undef;
}

sub getWorkingProtocol {
  my ($host, $section) = @_;
      
  foreach my $p (@{$protocols{$section}}) {
    next unless defined $data{$host}{$section}{$p};
    return $p;
  }
  undef;
}

sub isProtocolHTTPWorking {
  my ($host, $section) = @_;

  return defined $data{$host}{$section}{'http'};
}

sub getHostInfo {
  my ($hostname) = @_;

  return 0 if defined $IPs{$hostname};

  $? = 0; # huh, why is that needed?
  my ($name,$aliases,$addrtype,$length,@addrs) = gethostbyname($hostname);

  #print "HUUUU: $hostname $?\n";
  return 0 if ($?);

  foreach my $h ($hostname, $name, split(/\s+/, $aliases)) {
    next if $h eq '' || defined $IPs{$h};
    $IPs{$h} = [map { join(".", unpack('C4', $_)) } @addrs];
    print "IP: $h: ", join(", ", map { join(".", unpack('C4', $_)) } @addrs), "\n";
  }
  1;
}

sub areHostsEqual {
  my ($host1, $host2) = @_;

  return 0 unless defined $IPs{$host1} && defined $IPs{$host2};
  my @h1 = @{$IPs{$host1}};
  my @h2 = @{$IPs{$host2}};
  for (my $i = 0; $i <= $#h1; $i++) {
    for (my $j = 0; $j <= $#h2; $j++) {
      return 1 if $h1[$i] eq $h2[$j];
    }
  }
  0;
}

sub getOfficialHostname {
  my ($h, $section) = @_;

  return $h if (grep(/^$h$/, keys %addrs));
  return $h unless defined $IPs{$h};
  for my $a (keys %addrs) {
    next unless defined $IPs{$a};
    foreach my $i (@{$IPs{$a}}) {
      return $a if (grep(/^$i$/, @{$IPs{$h}}) &&
                    @{$IPs{$a}} == 1 && # NO DNS round robin entries...
                    defined $addrs{$a}{$section}{tracedir});
    }
  }
  return $h;
}

sub doStep {
  my ($host, $section, $protocol) = @_;

  # get path since we can have protocol specific paths
  my $path = getPathForProtocol($host, $section, $protocol);
  return unless defined $path;

  DBG(">>>> $host - $section - $protocol - $path\n");

  unless (defined $data{$host}{$section}{timestamps_sec}) {
    next unless (defined $addrs{$host}{$section}{tracedir});
    my $pa = $path;
    $pa .= '/' if ($pa !~ /\/$/);
    $pa .= $addrs{$host}{$section}{tracedir};
    my $listing = getDirListing("$protocol://$host$pa");
    if ($listing !~ /^ERROR: /m) {
      my @files = getLinkFilesOutOfListing($protocol, $listing);
      @files = cleanOutNonMirrorTraceFiles(uniqueList(@files));
      DBG("Got upstream mirrors (via $protocol): ".join(", ", @files), "\n");

      #print STDERR "TODO: check for ", scalar @files, " == 1 --> client failure!\n";

      # some badly configured servers return HTTP 200 codes even
      # if they should return 404...
      next unless (defined $addrs{$host}{$section}{mastertracefile});
      if (grep(/^$addrs{$host}{$section}{mastertracefile}$/, @files)) {
        $data{$host}{$section}{$protocol} = -1;
        foreach my $h (@files) {
          $data{$host}{$section}{timestamps_str}{$h} = undef;
          $data{$host}{$section}{timestamps_sec}{$h} = undef;
        }
      } else {
#        warn "Missing master file $addrs{$host}{$section}{mastertracefile} on $host\n";
        if ($listing =~ /<html>/i) {
          $listing = "ERROR: ".$listing if ($listing !~ /^ERROR: /);
          $listing = removeHTMLTags($listing);
        }
        $data{$host}{$section}{$protocol} = getErrorNr($listing, $protocol);
      }

    } else {
      $data{$host}{$section}{$protocol} = getErrorNr($listing, $protocol);
    }
	  
  } elsif ((my $file = getUndefinedTimestampFile($host, $section)) &&
           (!defined $data{$host}{$section}{$protocol} ||
	     $data{$host}{$section}{$protocol} == -1)) {
    my $pa = $path;
    $pa .= '/' if ($pa !~ /\/$/);
    $pa .= $addrs{$host}{$section}{tracedir}.'/'.$file;
    DBG("getting tracefile via $protocol://$host$pa\n");
    my $d = getFile("$protocol://$host$pa");
    DBG("output: $d\n");

    # some badly configured servers return a HTTP code 200 even
    # if they could not find a file and present a nicely formated
    # error message
    if (length($d) > 60) {
      $d = "ERROR: ".$d if ($d !~ /^ERROR: /);
      $d = removeHTMLTags($d);
    }
    if ($d !~ /^ERROR: /m) {
      $data{$host}{$section}{$protocol} = -1;
      $data{$host}{$section}{timestamps_str}{$file} = $d;
      $data{$host}{$section}{timestamps_sec}{$file} = getSecondsOfDatestring($d);
      if ($data{$host}{$section}{timestamps_sec}{$file} =~ /^ERROR: /) {
        $data{$host}{$section}{timestamps_sec}{$file} = 0;
      }
    } else {
      $data{$host}{$section}{$protocol} = getErrorNr($d, $protocol);
    }

  } elsif (!defined $data{$host}{$section}{updateInProgess} &&
           checkUpdateInProgress($section)) {
    DBG("Checking if update in progress\n");
    checkIfUpdateIsInProgress($protocol, $host, $path, $section);

  } else {
    # done
    DBG("done\n");
    return 0;
  }
  1;
}


######################################################################

Getopt::Long::config("pass_through");
my $optret = GetOptions(@arg_options);

if (defined $ARGV[0] && $ARGV[0] eq 'get') {

  parseMirrorsMasterList();
  
  $timestamps{data_capture_start} = time();

  foreach my $host (keys %addrs) {
    next if ($host !~ /$hostpattern/);
  
    foreach my $section (@sections) {
  
      foreach my $protocol (@{$protocols{$section}}) {
        next if (defined $addrs{$host}{checkProtocol} &&
                 !grep(/^$protocol$/, @{$addrs{$host}{checkProtocol}}));
  
	# following steps:
	# - get directory listing
	# - if master-files not in dir-listing -> error
	# - get all timestamp files from dir-listing
	# - check if update in progress...

        doStep($host, $section, $protocol);
  
  
      } # foreach protocol
      
      if (defined $data{$host}{$section}{timestamps_sec}) {
        # ok, we've got at least one protocol that works
	my $protocol = undef;
	# find it
	foreach (@{$protocols{$section}}) {
           $protocol = $_, last
	     if (defined $data{$host}{$section}{$_} && 
	         $data{$host}{$section}{$_} == -1);
	}
	if (defined $protocol) {
	  while (doStep($host, $section, $protocol)) {}
	} else {
	  print STDERR "BIG INTERNAL ERROR!\n"; 
	}
      }
      
    } # foreach section (main, cd, www)

  } # foreach host

  # get the IPs of all hostnames to find hosts with more than one name
  # (e.g. real name and debian.org alias)

  
  if (open(I, $DataFileIP)) {
    my $dat;
    while (<I>) {
      $dat .= $_;
    }
    close I;
    eval $dat;
  }
  
  print "$IPDataCaptureTime + $IPListRefreshTime\n";
  if ($IPDataCaptureTime + $IPListRefreshTime < time) {
    print "IPs:\n";
    foreach my $host (keys %addrs) {
      print "$host\n";
      getHostInfo($host);
    }
    foreach my $host (keys %data) {
      print "$host\n";
      getHostInfo($host);
      foreach my $section (keys %{$data{$host}}) {
        print "  $section\n";
        if (defined $data{$host}{$section}{timestamps_str}) {
          foreach my $tsh (keys %{$data{$host}{$section}{timestamps_str}}) {
  	    print "    $tsh\n";
            getHostInfo($tsh);
	  }
        }
      }
    }
  
    open(I, ">$DataFileIP") || die $!;
    $Data::Dumper::Indent = 1;
    $IPDataCaptureTime = time;
    print I Data::Dumper->Dump
       ([$IPDataCaptureTime, \%IPs], [qw/IPDataCaptureTime *IPs/]);
    close I;
  }
  
  open(A, ">$DataFile") || die $!;
  $Data::Dumper::Indent = 1;
  $timestamps{data_capture_end} = time();
  print A Data::Dumper->Dump
     ([\%timestamps, \%addrs, \%data, \@errors_filt, \@errors_full],
      [qw/*timestamps *addrs  *data   *errors_filt   *errors_full/]);
  close A;
  
} else {

  open(A, "$DataFile") || die $!;
  my $dat;
  while (<A>) {
    $dat .= $_;
  }
  close A;
  eval $dat;

  open(I, $DataFileIP) || die $!;
  $dat = '';
  while (<I>) {
    $dat .= $_;
  }
  close I;
  eval $dat;

  DBG("Using data created between ",
    scalar localtime $timestamps{data_capture_start}, " and ",
    scalar localtime $timestamps{data_capture_end}, "\n");
}








####### create HTML file out of the generated data... ######

DBG("Creating HTML files ($HtmlDir/$HtmlFile)\n\n");

open(H, ">$HtmlDir/$HtmlFile") || die $!;

my $dts_s   = (scalar gmtime $timestamps{data_capture_start})." UTC";
my $dts_e   = (scalar gmtime $timestamps{data_capture_end})." UTC";
my $now_utc = (scalar gmtime time)." UTC";
print H <<EOF;
<html><head><title>Debian Mirror Checker</title></head>
<style type="text/css">
<!--
  .inv
  {
      	text-decoration: none;
	color: black;
  }
  .inv:hover
  {
	text-decoration: underline;
	color: blue;
  }
  .mastertime
  {
	text-decoration: none;
	color: black;
  }
  .outofdate
  {
	color: brown;
	text-decoration: none;
  }
  .misplaced
  {
  	color: red;
	text-decoration: none;
  }
  .misplaced:hover
  {
  	text-decoration: underline;
  }
-->
</style>
<body bgcolor="white">
<TABLE border="0" width="100%" cellpadding="3" cellspacing="0" align="center" summary="">
<TR>
  <TD>
    <A HREF="http://www.debian.org/logos/">
    <IMG src="http://www.debian.org/Pics/logo-50.jpg" border="0" hspace="0" vspace="0" alt="" width="50" height="61"></A>
    <IMG src="http://www.debian.org/Pics/debian.jpg" border="0" hspace="0" vspace="0" alt="Debian Project" width="179" height="61">
  </TD>
  <td align="right" style="font-size: 75%">
    Data capturing time window:<br>$dts_s<br> - $dts_e<br>
    HTML-file creation time: $now_utc
  </td>
</TR>
</TABLE>
<h2 align="center">Debian Mirror Checker</h2>
EOF

sub validSection {
  my ($host, $sect) = @_;
  return 1 if (defined $addrs{$host}{$sect}{path});
  foreach (@{$protocols{$sect}}) {
    return 1 if (defined $addrs{$host}{$sect}{"path_$_"});
  }
  0;
}

use constant TRACE_NO_MASTERFILE               => 1;
use constant TRACE_TIMESTAMPS_BEFORE_MASTER    => 2;
use constant TRACE_INVALID_DATES               => 3;
use constant TRACE_NOT_DOWNLOADABLE            => 4;
use constant TRACE_NO_PRIMARY                  => 5;
use constant TRACE_NO_SECONDARY                => 6;
use constant TRACE_NO_TRACEFILE_FOR_OWN_MIRROR => 7;
use constant TRACE_NO_TRACEFILES_AT_ALL        => 8;

my %TraceTypeText =
(
  &TRACE_NO_MASTERFILE =>
    'No master file found',
  &TRACE_TIMESTAMPS_BEFORE_MASTER =>
    'Older (non-valid) timestamp files found',
  &TRACE_INVALID_DATES =>
    'Timestamp files contain invalid dates',
  &TRACE_NOT_DOWNLOADABLE =>
    'Trace files are not downloadable',
  &TRACE_NO_PRIMARY =>
    'Mirror lacks trace files from their upstream, it is not a primary',
  &TRACE_NO_SECONDARY =>
    'Mirror lacks trace files from their upstream, it is not a secondary',
  &TRACE_NO_TRACEFILE_FOR_OWN_MIRROR =>
    'The local trace file is missing',
  &TRACE_NO_TRACEFILES_AT_ALL =>
    'There are no trace files at all',
);

use constant MIRROR_PRIMARY   => 1;
use constant MIRROR_SECONDARY => 2;
use constant MIRROR_LEAF      => 3;
use constant MIRROR_UNKNOWN   => 4;

my %mirrorHTMLIDs =
(
  &MIRROR_PRIMARY   => '<b>P</b>',
  &MIRROR_SECONDARY => '<b>S</b>',
  &MIRROR_LEAF      => 'L',
  &MIRROR_UNKNOWN   => '?',
);
my %mirrorTypes =
(
  'Push-Primary'   => MIRROR_PRIMARY,
  'Push-Secondary' => MIRROR_SECONDARY,
  'leaf'           => MIRROR_LEAF,
);

sub getMirrorType {
  my ($host) = @_;
  return $mirrorTypes{$addrs{$host}{info}{Type}}
     if defined $addrs{$host}{info}{Type} and
        defined $mirrorTypes{$addrs{$host}{info}{Type}};
 # return $addrs{$host}{info}{Type}
 #    if defined $addrs{$host}{info}{Type};
  return MIRROR_UNKNOWN;
}

sub getMirrorHTMLIDs {
  my ($host) = @_;
  return $mirrorHTMLIDs{getMirrorType($host)};
}


sub addTraceEntry {
  my ($host, $section, $entry) = @_;
  push @{$data{$host}{$section}{tracestat}}, $entry;
}

sub getTraceEntries {
  my ($host, $section) = @_;
  return () unless defined $data{$host}{$section}{tracestat};
  @{$data{$host}{$section}{tracestat}};
}

sub isTraceEntry {
  my ($host, $section, $nr) = @_;

  return 0 unless defined $data{$host}{$section}{tracestat};
  foreach my $t (@{$data{$host}{$section}{tracestat}}) {
    return 1 if $nr == $t;
  }
  return 0;
}

sub computeTraceStates {

   foreach my $section (@sections) {
     foreach my $host (keys %data) {
       next unless defined $data{$host}{$section};
         
       # TRACE_NO_TRACEFILES_AT_ALL
       addTraceEntry($host, $section, TRACE_NO_TRACEFILES_AT_ALL)
         unless defined $data{$host}{$section}{timestamps_str};

       # TRACE_NO_MASTERFILE
       # TRACE_TIMESTAMPS_BEFORE_MASTER
       my $ms = masterSeconds($host, $section);
       if (!defined $ms || $ms == 0) {
         addTraceEntry($host, $section, TRACE_NO_MASTERFILE);
       } else {
         foreach my $k (keys %{$data{$host}{$section}{timestamps_sec}}) {
           if (defined $data{$host}{$section}{timestamps_sec}{$k} &&
	               $data{$host}{$section}{timestamps_sec}{$k} != 0 &&
	               $data{$host}{$section}{timestamps_sec}{$k} < $ms) {
             addTraceEntry($host, $section, TRACE_TIMESTAMPS_BEFORE_MASTER);
	     last;
           }
         }
       }

       # TRACE_INVALID_DATES
       foreach my $k (keys %{$data{$host}{$section}{timestamps_sec}}) {
         if (defined $data{$host}{$section}{timestamps_sec}{$k} &&
	             $data{$host}{$section}{timestamps_sec}{$k} == 0) {
           addTraceEntry($host, $section, TRACE_INVALID_DATES);
	   last;
         }
       }
       
       # TRACE_NOT_DOWNLOADABLE
       # not implemented yet...

       my $mirror_type = getMirrorType($host);
       my $credit;
       # TRACE_NO_PRIMARY
       if ($mirror_type != MIRROR_PRIMARY) {
         $credit = 1;
         $credit++ if (defined $ms && $ms != 0);
	 $credit++
	   if (defined $data{$host}{$section}{timestamps_str}{$host});
	 addTraceEntry($host, $section, TRACE_NO_PRIMARY)
	   if (scalar keys %{$data{$host}{$section}{timestamps_str}} <
	   $credit);
       }
       

       # TRACE_NO_SECONDARY
       if ($mirror_type == MIRROR_SECONDARY) {
         $credit = 1;
         $credit++ if (defined $ms && $ms != 0);
	 $credit++
	   if (defined $data{$host}{$section}{timestamps_str}{$host});
	 addTraceEntry($host, $section, TRACE_NO_SECONDARY)
	   if (scalar keys %{$data{$host}{$section}{timestamps_str}} <
	   $credit);
       }

       # TRACE_NO_TRACEFILE_FOR_OWN_MIRROR
       my $bo = defined $data{$host}{$section}{timestamps_str}{$host};
       foreach my $h (keys %{$data{$host}{$section}{timestamps_str}}) {
         last if $bo;
         $bo = 1 if getOfficialHostname($h, $section) eq $host;
       }
       addTraceEntry($host, $section, TRACE_NO_TRACEFILE_FOR_OWN_MIRROR)
         unless $bo;
     }

   }
  
}

sub printSectionInfo {
  my $sect = shift;
  my $i = 1;
  my $master_type = ($sect eq 'www')?'www':'ftp';

  print H "<h2><a name=\"sect_$sect\">Archive: $sect</h2>\n\n<ul>\n";

  my $oldtime = undef;
  for my $host (sort {my ($aa, $bb) =
                      (masterSeconds($a, $sect), masterSeconds($b, $sect));
                      ((defined $bb)?$bb:0) <=> ((defined $aa)?$aa:0)} keys %data) {
    next unless (defined $data{$host}{$sect});
    next unless validSection($host, $sect);

    if ($openedfile{$host}++ < 2) { # hasn't been opened before
      if (-f "$HtmlDir/$host.html") {
        unlink "$HtmlDir/$host.html" or die "can't remove $HtmlDir/$host.html: $!";
      }
    }
    open M, ">>$HtmlDir/$host.html" or die "can't write to $HtmlDir/$host.html: $!";
    if ($openedfile{$host}++ < 2) { # hasn't been opened before
      print M "<html>\n<head><title>Debian Mirror Checker: $host</title></head>\n<body>\n\n";
      print M "<h1 align=center>Debian mirror $host</h1>\n";
    }

    print M "<h2><a name=\"sect_$sect\">Archive: $sect</h2>\n\n";

    my $ms = masterSeconds($host, $sect);
    if (defined $ms) {
      $i++ 
        if (defined $oldtime && $oldtime > $ms);
      $oldtime = $ms;
    }

    print H "<li>$i...<a href=\"$host.html#sect_$sect\">$host</a> ";

    print M "<p>Level of freshness: $i</p>\n";

    print H " [".getMirrorHTMLIDs($host)."] ";

    die "can't find Type for $host!" unless defined $addrs{$host}{info}{Type};
    print M "<p>Type: ".$addrs{$host}{info}{Type}."</p>\n";

    # master time
    my $timestr = masterTimeString($host, $sect);
    print M "<p>Master time stamp: ";
    unless (defined $timestr) {
      print H ' [<span class="outofdate">master time stamp N/A</span>] ';
      print M '<div class="outofdate">N/A</div>';
    } elsif ($timestr eq '') {
      print H ' [<span class="outofdate">master time stamp missing!</span>] ';
      print M '<div class="outofdate">No master file!</div>';
    } else {
      my $outofdateclass = 
       ($ms < $timestamps{data_capture_start} - $OutOfDateTime)?
        'class="outofdate"':'class="mastertime"';
      if (defined (my $p = getWorkingProtocol($host, $sect))) {
        my $path = getPathForProtocol($host, $sect, $p);
        $timestr = "<a $outofdateclass ".
	  "href=\"$p://$host$path/$addrs{$host}{$sect}{tracedir}/".
	  "$addrs{$host}{$sect}{mastertracefile}\">$timestr</a>";
      }
      print M "$timestr";
    }

    # trace status
    my @ts = getTraceEntries($host, $sect);
    if (@ts and defined $ms) {
      print H " [<a href=\"#tracelegend\">trace</a>: ".join(',', @ts)."] ";
      print M "<p>Trace status:\n<ul>";
      foreach my $traceerror (@ts) {
        print M "<li>$traceerror: $TraceTypeText{$traceerror}\n";
      }
      print M "</ul>\n";
    }

    # Update in progress
    if (checkUpdateInProgress($sect)) {
      if ((defined $data{$host}{$sect}{updateInProgess} &&
                   $data{$host}{$sect}{updateInProgess} == 1)) {
        print H " [UIP!] ";
        print M "<p>Checked while update was in progress!\n";
      }
    }
    print M "<p>Protocols:</p>\n<ul>\n";
    foreach my $p (@{$protocols{$sect}}) {
      my $pt; my $pth;
      if (defined $data{$host}{$sect}{$p}) {
        my $err = $data{$host}{$sect}{$p};
	my $path = getPathForProtocol($host, $sect, $p);
	my $link = "$p://$host$path";
	$link .= '/' if $link !~ /\/$/;
        if ($err == -1) {
          $pt = "<li>$p: <a class=\"inv\" href=\"$link\">ok</a>";
          $pth = "";
	} else {
	  $err++;
          $pt = "<li>$p: <b><a class=\"inv\" href=\"$link\">bad</a></b>:\n";
          $pth = " <b>[$p bad]</b> ";
	  my $s = $errors_full[$err-1];
          if (defined $s and $s ne "") {
            $s =~ s/\n/<br>$&/gs;
            $pt .= "<p>$s</p>\n";
          } else {
            $pt .= "<p>No error text!</p>\n";
          }
	}
      } else {
        $pt = "";
        $pth = "";
      }
      print M "$pt";
      print H "$pth";
    }
    print H "</li>\n";
    print M "</ul>\n";
    if ($sect eq $sections[-1]) { # last section
      print M "</body>\n</html>\n";
    }
    close M;
  }

  # ok, now the non-checked ones
  if (0 && $DisplayNonCheckedHosts) {
    for my $host (sort keys %addrs) {
      next if (defined $data{$host} && defined $data{$host}{$sect});
      next unless validSection($host, $sect);
  
      print H "<tr><td>&nbsp;</td><td>$host</td><td>".getMirrorHTMLIDs($host)."</td>\n";
      print H "<td> -- not checked -- </td>";
      print H "<td>&nbsp;</td>" if checkUpdateInProgress($sect);
      foreach my $p (@{$protocols{$sect}}) {
        if (defined $addrs{$host}{$sect}{"path_".$p}) {
	  my $url = "$p://$host".$addrs{$host}{$sect}{"path_$p"};
	  $url .= '/' if $url !~ /\/$/;
    	  print H "<td><a class=\"inv\" href=\"$url\">A</a></td>";
        } else {
          print H "<td>&nbsp;</td>";
        }
      }
      print H "</tr>\n";
    }
  }
  print H "</ul>\n";
}

sub printHierarchyList {
  my ($section, $pad, $z) = @_;

  print H " "x$pad, "<ul>\n";
  foreach (keys %$z) {
    next if $_ eq '__count__';
    my $rs = '';
    $rs .= " class=\"misplaced\""
      if (isTraceEntry($_, $section, TRACE_NO_PRIMARY) ||
          isTraceEntry($_, $section, TRACE_NO_SECONDARY));
    print H " "x($pad+1), "<li$rs>$_", 
      ($$z{$_}{__count__} > 1)?" ($$z{$_}{__count__})":'', "</li>\n";

    printHierarchyList($section, $pad+1, $$z{$_}) if keys %{$$z{$_}} > 1;
  }
  print H " "x$pad, "</ul>\n";
}

sub constructMatrix {
  my ($y, $x, $matrix, $hosts, %z) = @_;
  my $ysum=0;
  foreach my $z (keys %z) {
    next if $z eq '__count__';
    #print "II (",$y+$ysum,", $x): ", " "x$x, $z{$z}{'__count__'}, "  $z\n";
    $matrix->[$y+$ysum][$x] = { "__count__" => $z{$z}{'__count__'}, host => $z};
    $hosts->[$y+$ysum] = $z;
    my $i = 1;
    for ($i = 1; $i < $z{$z}{'__count__'}; $i++) {
      $matrix->[$y+$ysum+$i][$x] = { "__count__" => 0};
    }
    my $childsum = constructMatrix($y+$ysum, $x+1, $matrix, $hosts, %{$z{$z}});
    
    if ($childsum) {
      foreach my $pad (($childsum)..($z{$z}{'__count__'}-1)) {
        unless (defined $matrix->[$y+$ysum+$pad][$x+1]) {
          $matrix->[$y+$ysum+$pad][$x+1] = { "__count__" => 0, host => '' };
          #print "PP (",$y+$ysum+$pad,", ", $x+1, "): ", " "x$x, $z{$z}{'__count__'}, "\n";
	  $hosts->[$y+$ysum+$pad] = $z;
        }
      }
    }
    $ysum += $z{$z}{__count__};
  }
  #print "SUM: $ysum\n";
  $ysum;
}

sub printHierarchies {
  my ($section) = @_;

  my %a;
  my $longest = 0; 
  my $pa;
  foreach my $host (keys %data) {
    my $mts = masterTimeString($host, $section);
    next if !defined $mts || $mts eq '';
    if (defined $data{$host}{$section}{timestamps_sec} ) {
      my @tmp =
        sort { ($data{$host}{$section}{timestamps_sec}{$a} || 0xffffffff)
	      <=> ($data{$host}{$section}{timestamps_sec}{$b} || 0xffffffff) }
	      keys %{$data{$host}{$section}{timestamps_sec}};
      my $ms = masterSeconds($host, $section);
      $ms = 0 unless defined $ms;

      #print STDERR "Unoff: ", join(", ", @tmp), "\n";
      my @tmpoff = map { getOfficialHostname($_, $section) } @tmp;
      #print STDERR "Off: ", join(", ", @tmpoff), "\n";
      $longest = @tmp if $longest < @tmp;
      $pa = \%a;
      push @tmp, $host;
      push @tmpoff, $host;
      for (my $t = 0; $t <= $#tmp; $t++) {
	next
	  if (defined $data{$host}{$section}{timestamps_sec}{$tmp[$t]} &&
	              $data{$host}{$section}{timestamps_sec}{$tmp[$t]} < $ms);
	next if ($t < $#tmp && areHostsEqual($tmp[$t], $tmp[$t+1]));
	
        #print "$tmpoff[$t] ";
        $pa->{$tmpoff[$t]} = {} unless defined $pa->{$tmpoff[$t]};
	$pa->{$tmpoff[$t]}{__count__}++;
	$pa = $pa->{$tmpoff[$t]};
      }
      #print "\n";
    }
  }

  #$Data::Dumper::Indent = 1;
  #print Data::Dumper->Dump([\%a], ['*a']), "\n";

  my @matrix = ();
  my @hosts  = ();
  constructMatrix(0, 0,  \@matrix, \@hosts, %a);

  #$Data::Dumper::Indent = 1;
  #print Data::Dumper->Dump([\@matrix], ['*matrix']), "\n";

  #print join("_", map { (defined)?$_:'U' }@hosts), "\n";

  my $maxwidth = 0;
  for (my $y=0; $y <= $#matrix; $y++ ) {
    $maxwidth = @{$matrix[$y]} if @{$matrix[$y]} > $maxwidth;
  }
  print H "<table style=\"font-size: 60%\" align=\"center\" border=\"1\">\n";
  print H "<tr>";
  my @headertitles = qw(Host Master Primary Secondary/Leaf Leaf...);
  $maxwidth = @headertitles-1 if @headertitles <= $maxwidth;
  for (0..$maxwidth) {
    print H "<th>$headertitles[$_]</th>";
  }
  print H "</tr>\n";

  for (my $y=0; $y <= $#matrix; $y++ ){
    # we prefer HTTP for links
    my $p = 'http';
    $p = getWorkingProtocol($hosts[$y], $section)
      if (!isProtocolHTTPWorking($hosts[$y], $section));
    next unless defined $p;

    print H " <tr>\n  <td><i>";
    my $url = "$p://".$hosts[$y].getPathForProtocol($hosts[$y], $section, $p);
    $url .= '/' if $url !~ /\/$/;
    print H "<a class=\"inv\" href=\"$url\">",
      ((defined $hosts[$y])?$hosts[$y]:'&nbsp;'), "</a>";
    print H "</i></td>\n";

    for (my $x=0; $x < @{$matrix[$y]}; $x++) {
      if (defined $matrix[$y][$x]) {
        if ($matrix[$y][$x]{__count__}) {
	  my $host = $matrix[$y][$x]{host};
	  my $count = $matrix[$y][$x]{__count__};
	  my $td;
	  if (defined ($p = getWorkingProtocol($host, $section))) {
	    $p = 'http' if isProtocolHTTPWorking($host, $section);
	    $td = $addrs{$host}{$section}{tracedir};
	    $url = "$p://".$host.getPathForProtocol($host, $section, $p).'/'.$td;
	    $url .= '/' if $url !~ /\/$/;
          }
	  my $rs = '';
	  my $as = '';
	  $rs .= " rowspan=\"$count\""  if $count > 1;
	  if (isTraceEntry($host, $section, TRACE_NO_PRIMARY) ||
	       isTraceEntry($host, $section, TRACE_NO_SECONDARY)) {
            $as = ' class="misplaced"';
	    $rs .= $as if !defined $td;
	  } else {
	    $as .= ' class="inv"';
	  }
          print H 
	    "  <td$rs>", (defined $td)?"<a$as href=\"$url\">":'',
	      ($count > 1)?($count.'-'):'', $host, 
	    (defined $td)?'</a>':'', "</td>\n"

        } elsif (defined $matrix[$y][$x]{host}) {
          print H "  <td> &lt;----- </td>\n";
	}
      }
    }
    print H " </tr>\n";
  }
  print H "</table>\n";

  print H "<p>&nbsp;</p>\n";
  print H "<div style=\"font-size: 90%\">\n";
  printHierarchyList($section, 0, \%a);
  print H "</div>\n";
}

## ####### ####### ###### # #####

print H "<p align=\"center\">".join(", ", map {"<a href=\"#sect_$_\">$_</a>" } @sections);

computeTraceStates();

foreach my $sect (@sections) {
  print H "<p align=\"center\"><a href=\"#legend\">see legend</a></p>";
  printSectionInfo($sect);
  print H '<p>&nbsp;</p>';
#  printHierarchies($sect);
}

# legend
print H <<EOF;
<h3><a name="legend">Legend</a></h3>
<table border="0">
<tr>
  <td valign="top">UIP!</td>
  <td>Archive_update_in_progress file found</td>
</tr>
<tr>
  <td valign="top">T</td>
  <td>Type:
      <ul>
        <li>P: Push-Primary
        <li>S: Push-Secondary
        <li>L: Leaf
        <li>?: not in DB (will be leaf, of course)
      </ul>
  </td>
</tr>
</table>
EOF

print H "<p><a name=\"tracelegend\">Trace errors</a>:\n<table>\n";
foreach my $k (keys %TraceTypeText) {
  print H "<tr><td>$k:&nbsp;</td><td>$TraceTypeText{$k}</td></tr>\n";
}
print H "</table></p>\n";

print H <<EOF;
<hr noshade size="1">
HostPattern: $hostpattern

</body>
</html>
EOF
close H;
