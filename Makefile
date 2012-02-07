# This is a makefile for GNU Prolog compiler gplc
#
# NOTE: you need also GNU C compiler gcc to be able to compile the program
# using this makefile

GPLC_OPTIONS=--full-inline-asm --no-top-level --no-debugger --min-fd-bips\
	 --strip -C o3 --c-compiler gcc

rhino: rhino.pro
	gplc $(GPLC_OPTIONS) rhino.pro
