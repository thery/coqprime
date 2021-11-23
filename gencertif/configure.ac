# USAGE NOTES
# OS specific include and library paths can be given on the configure command line with e.g.
# ./configure CPPFLAGS=-I/opt/local/include LDFLAGS=-L/opt/local/lib
# We can't use automakes pkg-config interface because ecm usually doesn't have a pkgconfig gile.

# Initialize autoconf(name, version, bugreports)
AC_INIT([CoqPrime], [8.14], [https://github.com/thery/coqprime/issues])

# Find C compiler
AC_PROG_CC

# Check for libraries using the C compiler for checks
AC_LANG(C)

# GCC requires -lm for math functions like "log", other compilers don't.
# So check for -lm but don't throw an error if it is not there.
AC_CHECK_LIB(m, log)

# Check for the GNU multiple precision arithmetic library.
# Use th emethod recommended here: https://gmplib.org/manual/Autoconf
AC_CHECK_LIB(gmp, __gmpz_init, , AC_MSG_ERROR([Unable to find library 'gmp']))

# Check for the availablitiy of the Elliptic Curve Method library from
# https://gitlab.inria.fr/zimmerma/ecm
AC_CHECK_LIB(ecm, ecm_init, , AC_MSG_ERROR([Unable to find library 'gmp-ecm']))

# Write make file
AC_CONFIG_FILES([Makefile])
AC_OUTPUT
