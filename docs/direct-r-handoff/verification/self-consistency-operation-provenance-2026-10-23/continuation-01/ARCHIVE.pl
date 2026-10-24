use strict;
use warnings;
use utf8;
use File::Basename qw(dirname);
use File::Path qw(make_path);
use IO::Compress::Gzip qw(gzip $GzipError);
use IO::Uncompress::Gunzip qw(gunzip $GunzipError);
use Digest::SHA qw(sha256_hex);
use Encode qw(decode FB_CROAK);

my $archive = dirname(__FILE__);
make_path("$archive/raw");
open(my $manifest, '<:encoding(UTF-8)', "$archive/FILES.tsv") or die $!;
my $count = 0;
while (my $line = <$manifest>) {
    chomp $line;
    my ($name, $source) = split /\t/, $line, 2;
    die "Invalid target name" unless $name =~ /\A[A-Za-z0-9_.-]+\z/;
    open(my $input, '<:raw', $source) or die "$source: $!";
    my $bytes = do { local $/; <$input> };
    $bytes = '' unless defined $bytes;
    gzip \$bytes => "$archive/raw/$name.gz", Time => 0, Minimal => 1
        or die $GzipError;
    my $restored;
    gunzip "$archive/raw/$name.gz" => \$restored or die $GunzipError;
    die "Raw mismatch: $name" unless $bytes eq $restored;
    my $text_bytes = $bytes;
    my $normal = decode('UTF-8', $text_bytes, FB_CROAK);
    if (length $normal) {
        $normal =~ s/[ \t]+$//mg;
        $normal =~ s/\n+\z//;
        $normal .= "\n";
    }
    open(my $readable_input, '<:raw', "$archive/$name") or die $!;
    my $readable_bytes = do { local $/; <$readable_input> };
    $readable_bytes = '' unless defined $readable_bytes;
    my $readable = decode('UTF-8', $readable_bytes, FB_CROAK);
    die "Readable mismatch: $name" unless $normal eq $readable;
    print "$name\traw-ok\tnormalized-ok\t", sha256_hex($bytes), "\n";
    ++$count;
}
print "TOTAL\t$count\traw-ok\t$count\tnormalized-ok\n";
