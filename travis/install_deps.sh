#!/bin/sh
mkdir -p cache

# LLVM
case $LLVM_VERSION in
    "3.3")
        LLVM_URL="http://llvm.org/releases/$LLVM_VERSION/clang+llvm-$LLVM_VERSION-amd64-Ubuntu-12.04.2.tar.gz"
        ;;
    "3.4")
        LLVM_URL="http://llvm.org/releases/$LLVM_VERSION/clang+llvm-$LLVM_VERSION-x86_64-unknown-ubuntu12.04.tar.xz"
	;;
    "3.9.1")
	LLVM_URL="http://llvm.org/releases/$LLVM_VERSION/clang+llvm-$LLVM_VERSION-x86_64-linux-gnu-ubuntu-16.04.tar.xz"
	;;
    ?*)
	LLVM_URL="http://llvm.org/releases/$LLVM_VERSION/clang+llvm-$LLVM_VERSION-x86_64-linux-gnu-ubuntu-14.04.tar.xz"
	;;
esac
LLVM_DEP="cache/$LLVM_VERSION.tar.xz"
LLVM_DIR="cache/clang+llvm-$LLVM_VERSION"

echo $LLVM_URL
echo $LLVM_DEP
echo $LLVM_DIR

# download and install
if [ ! -f $LLVM_DEP ] ; then
    echo "Downloading LLVM"
    wget $LLVM_URL -O $LLVM_DEP
    if [ ! $? -eq 0 ]; then
	echo "Error: Download failed"
	rm $LLVM_DEP || true
	exit 1
    fi
else
    echo "Found Cached Archive"
fi

if [ ! -d $LLVM_DIR ] ; then
    echo "Extracting LLVM"
    tar -xf $LLVM_DEP -C cache/
    if [ ! $? -eq 0 ]; then
	echo "Error: Extraction Failed"
	rm $LLVM_DEP || true
	exit 1
    fi
    case $LLVM_VERSION in
        "3.3")
            mv cache/clang+llvm-$LLVM_VERSION-amd64-Ubuntu-12.04.2 cache/clang+llvm-$LLVM_VERSION
	    ;;
        "3.4")
            mv cache/clang+llvm-$LLVM_VERSION-x86_64-unknown-ubuntu12.04 cache/clang+llvm-$LLVM_VERSION
	    ;;
        3.5.*)
	    mv cache/clang+llvm-$LLVM_VERSION-x86_64-linux-gnu cache/clang+llvm-$LLVM_VERSION
	    ;;
	"3.9.1")
	    mv cache/clang+llvm-$LLVM_VERSION-x86_64-linux-gnu-ubuntu-16.04 cache/clang+llvm-$LLVM_VERSION
	    ;;
	?*)
	    mv cache/clang+llvm-$LLVM_VERSION-x86_64-linux-gnu-ubuntu-14.04 cache/clang+llvm-$LLVM_VERSION
	    ;;
    esac
else
    echo "Found Cached Installation"
fi
