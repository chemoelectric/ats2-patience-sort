#
# Copyright © 2022 Barry Schwartz
#
# This program is free software: you can redistribute it and/or
# modify it under the terms of the GNU General Public License, as
# published by the Free Software Foundation, either version 3 of the
# License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.
#
# You should have received copies of the GNU General Public License
# along with this program. If not, see
# <https://www.gnu.org/licenses/>.
#

.DELETE_ON_ERROR:

ACLOCAL_AMFLAGS = -I m4 --install
AUTOMAKE_OPTIONS =
AUTOMAKE_OPTIONS += foreign
AUTOMAKE_OPTIONS += subdir-objects
AUTOMAKE_OPTIONS += -Wno-portability

include $(top_srcdir)/aminclude_static.am
@GNU@ include $(top_srcdir)/silent-rules.mk
@GNU@ -include ats-dependencies/*.mk

EXTRA_DIST =
MOSTLYCLEANFILES =
CLEANFILES =
DISTCLEANFILES =
BUILT_SOURCES =
AM_CPPFLAGS =
AM_CFLAGS =
AM_LDFLAGS =
LDADD =
bin_PROGRAMS =
lib_LTLIBRARIES =
EXTRA_PROGRAMS =
nobase_nodist_pkginclude_HEADERS =
nodist_pkgconfig_DATA =

EXTRA_DIST += $(srcdir)/silent-rules.mk
EXTRA_DIST += COPYING
EXTRA_DIST += INSTALL
EXTRA_DIST += README
EXTRA_DIST += AUTHORS

DISTCLEANFILES += Makefile
DISTCLEANFILES += GNUmakefile

AM_CPPFLAGS += -I$(builddir)
AM_CPPFLAGS += -I$(srcdir)
AM_CPPFLAGS += -I$(PATSHOME)
AM_CPPFLAGS += -I$(PATSHOME)/ccomp/runtime/

LDADD += $(CODE_COVERAGE_LIBS)

CODE_COVERAGE_IGNORE_PATTERN =
CODE_COVERAGE_IGNORE_PATTERN += /usr/include/*
CODE_COVERAGE_IGNORE_PATTERN += /usr/include/*/*
CODE_COVERAGE_IGNORE_PATTERN += $(PATSHOME)/ccomp/runtime/*
CODE_COVERAGE_IGNORE_PATTERN += $(PATSHOME)/prelude/CATS/*

clean-local: code-coverage-clean tests-clean
distclean-local: code-coverage-dist-clean ats-includes-distclean

#---------------------------------------------------------------------
#
# Some GNU Make aids you might want to use.
#

comma := ,
empty :=
space := $(empty) $(empty)

# Escape things for sed expressions, etc.
escape = $(subst $$,\$$,$(subst ^,\^,$(subst ],\],$(subst [,\[,$(subst .,\.,$(subst \,\\,$(1)))))))

#--------------------------------------------------------------------------

PATSOPT_DEPS =

# DATS_WORDS_BIGENDIAN := \
# 	$(shell echo x $(DEFS) | \
# 		$(EGREP) -q '[[:space:]]-DWORDS_BIGENDIAN(=1)?([[:space:]]|$$)?' && \
# 				echo x'-DATS WORDS_BIGENDIAN=1' | \
# 		$(SED) -e 's|^x||')

# DATS_HAVE_ALIGNED_ACCESS_REQUIRED := \
# 	$(shell echo x $(DEFS) | \
# 		$(EGREP) -q '[[:space:]]-DHAVE_ALIGNED_ACCESS_REQUIRED(=1)?([[:space:]]|$$)?' && \
# 				echo x'-DATS HAVE_ALIGNED_ACCESS_REQUIRED=1' | \
# 		$(SED) -e 's|^x||')

AM_PATSOPTFLAGS =
# AM_PATSOPTFLAGS += $(DATS_WORDS_BIGENDIAN)
# AM_PATSOPTFLAGS += $(DATS_HAVE_ALIGNED_ACCESS_REQUIRED)
AM_PATSOPTFLAGS += -IATS $(builddir)
AM_PATSOPTFLAGS += -IATS $(srcdir)

TOTAL_PATSOPTFLAGS =
TOTAL_PATSOPTFLAGS += $(AM_PATSOPTFLAGS)
TOTAL_PATSOPTFLAGS += $(PATSOPTFLAGS)
TOTAL_PATSOPTFLAGS += $(XPATSOPTFLAGS)

TESTS_PATSOPTFLAGS =
TESTS_PATSOPTFLAGS += -IATS $(builddir)/tests
TESTS_PATSOPTFLAGS += -IATS $(srcdir)/tests

@GNU@ define write-dependencies-file =
@GNU@	$(MKDIR_P) ats-dependencies && \
@GNU@		echo $(1): $(shell ./list-ats-dependencies $(2)) \
@GNU@			> ats-dependencies/`echo $(@) | $(SED) 's|/|_057_|g'`.mk
@GNU@ endef

.PHONY: ats-includes-distclean
ats-includes-distclean:
	-rm -f -R ats-dependencies

if DEPENDENCY_TRACKING

%_sats.c: %.sats $(PATSOPT_DEPS) list-ats-dependencies
	@$(call write-dependencies-file,$(@),$(<))
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) -s $(<)

%_dats.c: %.dats $(PATSOPT_DEPS) list-ats-dependencies
	@$(call write-dependencies-file,$(@),$(<))
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) -d $(<)

%_tests.c: %.dats $(PATSOPT_DEPS) list-ats-dependencies
	@$(call write-dependencies-file,$(@),$(<))
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) \
			$(TESTS_PATSOPTFLAGS) -d $(<)

else !DEPENDENCY_TRACKING

%_sats.c: %.sats $(PATSOPT_DEPS)
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) -s $(<)

%_dats.c: %.dats $(PATSOPT_DEPS)
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) -d $(<)

%_tests.c: %.dats $(PATSOPT_DEPS)
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) \
			$(TESTS_PATSOPTFLAGS) -d $(<)

endif !DEPENDENCY_TRACKING

%_depsprog.c: %.dats $(PATSOPT_DEPS)
	@$(MKDIR_P) $(@D)
	$(call v,PATSOPT)$(PATSOPT) -o $(@) $(TOTAL_PATSOPTFLAGS) -d $(<)

#--------------------------------------------------------------------------
#
# The ATS2 library.
#

lib_LTLIBRARIES += libats2-patience-sort.la

PATIENCE_SORT_SATS = patience-sort/SATS/patience-sort.sats
PATIENCE_SORT_SATS_C = patience-sort/SATS/patience-sort_sats.c
EXTRA_DIST += $(PATIENCE-SORT_SATS)
CLEANFILES += $(PATIENCE-SORT_SATS_C)

nodist_libats2_patience_sort_la_SOURCES =
nodist_libats2_patience_sort_la_SOURCES += $(PATIENCE_SORT_SATS_C)

# SPOOKYHASH_PARAMETERS_HATS = spookyhash/HATS/spookyhash-parameters.hats
# EXTRA_DIST += $(SPOOKYHASH_PARAMETERS_HATS)

# SPOOKYHASH_ATS_PARAMETERS_HATS = spookyhash/HATS/spookyhash-ats-parameters.hats
# EXTRA_DIST += $(SPOOKYHASH_ATS_PARAMETERS_HATS)

# SPOOKYHASH_IMPL_CATS = spookyhash/CATS/spookyhash-implementation.cats
# EXTRA_DIST += $(SPOOKYHASH_IMPL_CATS)

# SPOOKYHASH_CATS = spookyhash/CATS/spookyhash.cats
# EXTRA_DIST += $(SPOOKYHASH_CATS)

# SPOOKYHASH_BYTE_ORDER_SATS = spookyhash/SATS/spookyhash-byte-order.sats
# SPOOKYHASH_BYTE_ORDER_SATS_C = spookyhash/SATS/spookyhash-byte-order_sats.c
# EXTRA_DIST += $(SPOOKYHASH_BYTE_ORDER_SATS)
# CLEANFILES += $(SPOOKYHASH_BYTE_ORDER_SATS_C)

# SPOOKYHASH_BYTE_ORDER_INC = spookyhash/DATS/include/spookyhash-byte-order.inc
# EXTRA_DIST += $(SPOOKYHASH_BYTE_ORDER_INC)

# SPOOKYHASH_TEMPLATES_SATS = spookyhash/SATS/spookyhash-templates.sats
# SPOOKYHASH_TEMPLATES_SATS_C = spookyhash/SATS/spookyhash-templates_sats.c
# EXTRA_DIST += $(SPOOKYHASH_TEMPLATES_SATS)
# CLEANFILES += $(SPOOKYHASH_TEMPLATES_SATS_C)

# SPOOKYHASH_TEMPLATES_INC = spookyhash/DATS/include/spookyhash-templates.inc
# EXTRA_DIST += $(SPOOKYHASH_TEMPLATES_INC)

# ARRAY_PRF_SATS = spookyhash/SATS/array_prf.sats
# ARRAY_PRF_SATS_C = spookyhash/SATS/array_prf_sats.c
# EXTRA_DIST += $(ARRAY_PRF_SATS)
# CLEANFILES += $(ARRAY_PRF_SATS_C)

# ARRAY_PRF_DATS = spookyhash/DATS/array_prf.dats
# ARRAY_PRF_DATS_C = spookyhash/DATS/array_prf_dats.c
# EXTRA_DIST += $(ARRAY_PRF_DATS)
# CLEANFILES += $(ARRAY_PRF_DATS_C)

# SPOOKYHASH_CASTS_SATS = spookyhash/SATS/spookyhash-casts.sats
# SPOOKYHASH_CASTS_SATS_C = spookyhash/SATS/spookyhash-casts_sats.c
# EXTRA_DIST += $(SPOOKYHASH_CASTS_SATS)
# CLEANFILES += $(SPOOKYHASH_CASTS_SATS_C)

# SPOOKYHASH_MEM_SATS = spookyhash/SATS/spookyhash-mem.sats
# SPOOKYHASH_MEM_SATS_C = spookyhash/SATS/spookyhash-mem_sats.c
# EXTRA_DIST += $(SPOOKYHASH_MEM_SATS)
# CLEANFILES += $(SPOOKYHASH_MEM_SATS_C)

# SPOOKYHASH_ALIGNMENT_SATS = spookyhash/SATS/spookyhash-alignment.sats
# SPOOKYHASH_ALIGNMENT_SATS_C = spookyhash/SATS/spookyhash-alignment_sats.c
# EXTRA_DIST += $(SPOOKYHASH_ALIGNMENT_SATS)
# CLEANFILES += $(SPOOKYHASH_ALIGNMENT_SATS_C)

# SPOOKYHASH_INTERNAL_TYPES_SATS = spookyhash/SATS/spookyhash-internal-types.sats
# SPOOKYHASH_INTERNAL_TYPES_SATS_C = spookyhash/SATS/spookyhash-internal-types_sats.c
# EXTRA_DIST += $(SPOOKYHASH_INTERNAL_TYPES_SATS)
# CLEANFILES += $(SPOOKYHASH_INTERNAL_TYPES_SATS_C)

# SPOOKYHASH_ARITHMETIC_SATS = spookyhash/SATS/spookyhash-arithmetic.sats
# SPOOKYHASH_ARITHMETIC_SATS_C = spookyhash/SATS/spookyhash-arithmetic_sats.c
# EXTRA_DIST += $(SPOOKYHASH_ARITHMETIC_SATS)
# CLEANFILES += $(SPOOKYHASH_ARITHMETIC_SATS_C)

# SPOOKYHASH_PROOFS_SATS = spookyhash/SATS/spookyhash-proofs.sats
# SPOOKYHASH_PROOFS_SATS_C = spookyhash/SATS/spookyhash-proofs_sats.c
# EXTRA_DIST += $(SPOOKYHASH_PROOFS_SATS)
# CLEANFILES += $(SPOOKYHASH_PROOFS_SATS_C)

# SPOOKYHASH_PROOFS_DATS = spookyhash/DATS/spookyhash-proofs.dats
# SPOOKYHASH_PROOFS_DATS_C = spookyhash/DATS/spookyhash-proofs_dats.c
# EXTRA_DIST += $(SPOOKYHASH_PROOFS_DATS)
# CLEANFILES += $(SPOOKYHASH_PROOFS_DATS_C)

# SPOOKYHASH_SATS = spookyhash/SATS/spookyhash.sats
# SPOOKYHASH_SATS_C = spookyhash/SATS/spookyhash_sats.c
# EXTRA_DIST += $(SPOOKYHASH_SATS)
# CLEANFILES += $(SPOOKYHASH_SATS_C)

# SPOOKYHASH_HASH128_DATS = spookyhash/DATS/spookyhash_hash128.dats
# SPOOKYHASH_HASH128_DATS_C = spookyhash/DATS/spookyhash_hash128_dats.c
# EXTRA_DIST += $(SPOOKYHASH_HASH128_DATS)
# CLEANFILES += $(SPOOKYHASH_HASH128_DATS_C)

# SPOOKYHASH_HASH64_DATS = spookyhash/DATS/spookyhash_hash64.dats
# SPOOKYHASH_HASH64_DATS_C = spookyhash/DATS/spookyhash_hash64_dats.c
# EXTRA_DIST += $(SPOOKYHASH_HASH64_DATS)
# CLEANFILES += $(SPOOKYHASH_HASH64_DATS_C)

# SPOOKYHASH_HASH32_DATS = spookyhash/DATS/spookyhash_hash32.dats
# SPOOKYHASH_HASH32_DATS_C = spookyhash/DATS/spookyhash_hash32_dats.c
# EXTRA_DIST += $(SPOOKYHASH_HASH32_DATS)
# CLEANFILES += $(SPOOKYHASH_HASH32_DATS_C)

# SPOOKYHASH_INCREMENTAL_DATS = spookyhash/DATS/spookyhash-incremental.dats
# SPOOKYHASH_INCREMENTAL_DATS_C = spookyhash/DATS/spookyhash-incremental_dats.c
# EXTRA_DIST += $(SPOOKYHASH_INCREMENTAL_DATS)
# CLEANFILES += $(SPOOKYHASH_INCREMENTAL_DATS_C)

# nodist_libats2_spookyhash_la_SOURCES =
# nodist_libats2_spookyhash_la_SOURCES += $(ARRAY_PRF_SATS_C)
# nodist_libats2_spookyhash_la_SOURCES += $(ARRAY_PRF_DATS_C)
# nodist_libats2_spookyhash_la_SOURCES += $(SPOOKYHASH_BYTE_ORDER_SATS_C)
# nodist_libats2_spookyhash_la_SOURCES += $(SPOOKYHASH_TEMPLATES_SATS_C)
# nodist_libats2_spookyhash_la_SOURCES += $(SPOOKYHASH_CASTS_SATS_C)
# nodist_libats2_spookyhash_la_SOURCES += $(SPOOKYHASH_MEM_SATS_C)
# nodist_libats2_spookyhash_la_SOURCES += $(SPOOKYHASH_ALIGNMENT_SATS_C)
# nodist_libats2_spookyhash_la_SOURCES += $(SPOOKYHASH_ARITHMETIC_SATS_C)
# nodist_libats2_spookyhash_la_SOURCES += $(SPOOKYHASH_INTERNAL_TYPES_SATS_C)
# nodist_libats2_spookyhash_la_SOURCES += $(SPOOKYHASH_PROOFS_SATS_C)
# nodist_libats2_spookyhash_la_SOURCES += $(SPOOKYHASH_PROOFS_DATS_C)
# nodist_libats2_spookyhash_la_SOURCES += $(SPOOKYHASH_SATS_C)
# nodist_libats2_spookyhash_la_SOURCES += $(SPOOKYHASH_DATS_C)
# nodist_libats2_spookyhash_la_SOURCES += $(SPOOKYHASH_HASH128_DATS_C)
# nodist_libats2_spookyhash_la_SOURCES += $(SPOOKYHASH_HASH64_DATS_C)
# nodist_libats2_spookyhash_la_SOURCES += $(SPOOKYHASH_HASH32_DATS_C)
# nodist_libats2_spookyhash_la_SOURCES += $(SPOOKYHASH_INCREMENTAL_DATS_C)

# nobase_nodist_pkginclude_HEADERS += $(SPOOKYHASH_SATS)
# nobase_nodist_pkginclude_HEADERS += $(SPOOKYHASH_CATS)
# nobase_nodist_pkginclude_HEADERS += $(SPOOKYHASH_PARAMETERS_HATS)

#--------------------------------------------------------------------------
#
# The C library.
#

# lib_LTLIBRARIES += libspookyhash.la

# libspookyhash_la_SOURCES =
# libspookyhash_la_SOURCES += spookyhash/spookyhash.h
# libspookyhash_la_SOURCES += spookyhash/spookyhash_hash128.c
# libspookyhash_la_SOURCES += spookyhash/spookyhash_hash64.c
# libspookyhash_la_SOURCES += spookyhash/spookyhash_hash32.c
# libspookyhash_la_SOURCES += spookyhash/spookyhash-incremental.c

# libspookyhash_la_LIBADD =
# libspookyhash_la_LIBADD += libats2-spookyhash.la

# nobase_nodist_pkginclude_HEADERS += spookyhash/spookyhash.h

#--------------------------------------------------------------------------

# EXTRA_PROGRAMS += tests/compute-reference-result
# CLEANFILES += tests/compute-reference-result
# tests_compute_reference_result_SOURCES =
# tests_compute_reference_result_SOURCES += tests/compute-reference-result.cpp
# tests_compute_reference_result_SOURCES += tests/SpookyV2.cpp
# tests_compute_reference_result_SOURCES += tests/SpookyV2.h
# tests_compute_reference_result_CPPFLAGS =
# tests_compute_reference_result_CPPFLAGS += $(AM_CPPFLAGS)
# tests_compute_reference_result_CPPFLAGS += -I$(builddir)/tests
# tests_compute_reference_result_CPPFLAGS += -I$(srcdir)/tests

# EXTRA_PROGRAMS += tests/try-spookyhash_hash128
# CLEANFILES += tests/try-spookyhash_hash128
# CLEANFILES += tests/try-spookyhash_hash128_tests.c
# tests_try_spookyhash_hash128_SOURCES =
# tests_try_spookyhash_hash128_SOURCES += tests/try-spookyhash_hash128_tests.c
# tests_try_spookyhash_hash128_DEPENDENCIES =
# tests_try_spookyhash_hash128_DEPENDENCIES += tests/try-spookyhash_hash128.dats
# tests_try_spookyhash_hash128_DEPENDENCIES += tests/try-spookyhash-common.hats
# tests_try_spookyhash_hash128_DEPENDENCIES += libats2-spookyhash.la
# tests_try_spookyhash_hash128_LDADD =
# tests_try_spookyhash_hash128_LDADD += libats2-spookyhash.la

# EXTRA_PROGRAMS += tests/try-spookyhash_hash64
# CLEANFILES += tests/try-spookyhash_hash64
# CLEANFILES += tests/try-spookyhash_hash64_tests.c
# tests_try_spookyhash_hash64_SOURCES =
# tests_try_spookyhash_hash64_SOURCES += tests/try-spookyhash_hash64_tests.c
# tests_try_spookyhash_hash64_DEPENDENCIES =
# tests_try_spookyhash_hash64_DEPENDENCIES += tests/try-spookyhash_hash64.dats
# tests_try_spookyhash_hash64_DEPENDENCIES += tests/try-spookyhash-common.hats
# tests_try_spookyhash_hash64_DEPENDENCIES += libats2-spookyhash.la
# tests_try_spookyhash_hash64_LDADD =
# tests_try_spookyhash_hash64_LDADD += libats2-spookyhash.la

# EXTRA_PROGRAMS += tests/try-spookyhash_hash32
# CLEANFILES += tests/try-spookyhash_hash32
# CLEANFILES += tests/try-spookyhash_hash32_tests.c
# tests_try_spookyhash_hash32_SOURCES =
# tests_try_spookyhash_hash32_SOURCES += tests/try-spookyhash_hash32_tests.c
# tests_try_spookyhash_hash32_DEPENDENCIES =
# tests_try_spookyhash_hash32_DEPENDENCIES += tests/try-spookyhash_hash32.dats
# tests_try_spookyhash_hash32_DEPENDENCIES += tests/try-spookyhash-common.hats
# tests_try_spookyhash_hash32_DEPENDENCIES += libats2-spookyhash.la
# tests_try_spookyhash_hash32_LDADD =
# tests_try_spookyhash_hash32_LDADD += libats2-spookyhash.la

# EXTRA_PROGRAMS += tests/try-spookyhash-incremental
# CLEANFILES += tests/try-spookyhash-incremental
# CLEANFILES += tests/try-spookyhash-incremental_tests.c
# tests_try_spookyhash_incremental_SOURCES =
# tests_try_spookyhash_incremental_SOURCES += tests/try-spookyhash-incremental_tests.c
# tests_try_spookyhash_incremental_DEPENDENCIES =
# tests_try_spookyhash_incremental_DEPENDENCIES += tests/try-spookyhash-incremental.dats
# tests_try_spookyhash_incremental_DEPENDENCIES += tests/try-spookyhash-common.hats
# tests_try_spookyhash_incremental_DEPENDENCIES += libats2-spookyhash.la
# tests_try_spookyhash_incremental_LDADD =
# tests_try_spookyhash_incremental_LDADD += libats2-spookyhash.la

# EXTRA_PROGRAMS += tests/try-spookyhash_hash128-misaligned
# CLEANFILES += tests/try-spookyhash_hash128-misaligned
# CLEANFILES += tests/try-spookyhash_hash128-misaligned_tests.c
# tests_try_spookyhash_hash128_misaligned_SOURCES =
# tests_try_spookyhash_hash128_misaligned_SOURCES += tests/try-spookyhash_hash128-misaligned_tests.c
# tests_try_spookyhash_hash128_misaligned_DEPENDENCIES =
# tests_try_spookyhash_hash128_misaligned_DEPENDENCIES += tests/try-spookyhash_hash128-misaligned.dats
# tests_try_spookyhash_hash128_misaligned_DEPENDENCIES += tests/try-spookyhash-common.hats
# tests_try_spookyhash_hash128_misaligned_DEPENDENCIES += libats2-spookyhash.la
# tests_try_spookyhash_hash128_misaligned_LDADD =
# tests_try_spookyhash_hash128_misaligned_LDADD += libats2-spookyhash.la

# EXTRA_DIST += tests/try-spookyhash_hash128.dats
# EXTRA_DIST += tests/try-spookyhash_hash64.dats
# EXTRA_DIST += tests/try-spookyhash_hash32.dats
# EXTRA_DIST += tests/try-spookyhash-incremental.dats
# EXTRA_DIST += tests/try-spookyhash-common.hats
# EXTRA_DIST += tests/try-spookyhash_hash128-misaligned.dats
# tests/try-spookyhash_hash128_tests.c: tests/try-spookyhash_hash128.dats
# tests/try-spookyhash_hash128_tests.c: tests/try-spookyhash-common.hats
# tests/try-spookyhash_hash64_tests.c: tests/try-spookyhash_hash64.dats
# tests/try-spookyhash_hash64_tests.c: tests/try-spookyhash-common.hats
# tests/try-spookyhash_hash32_tests.c: tests/try-spookyhash_hash32.dats
# tests/try-spookyhash_hash32_tests.c: tests/try-spookyhash-common.hats
# tests/try-spookyhash-incremental_tests.c: tests/try-spookyhash-incremental.dats
# tests/try-spookyhash-incremental_tests.c: tests/try-spookyhash-common.hats
# tests/try-spookyhash_hash128-misaligned_tests.c: tests/try-spookyhash_hash128-misaligned.dats
# tests/try-spookyhash_hash128-misaligned_tests.c: tests/try-spookyhash-common.hats

# EXTRA_DIST += $(srcdir)/tests/reference-for-seeds-eq-zero.dat
# EXTRA_DIST += $(srcdir)/tests/reference-for-hash128-seed.dat
# EXTRA_DIST += $(srcdir)/tests/reference-for-hash64-seed.dat
# EXTRA_DIST += $(srcdir)/tests/reference-for-hash32-seed.dat

# EXTRA_PROGRAMS += tests/try-spookyhash_hash128-c
# CLEANFILES += tests/try-spookyhash_hash128-c
# tests_try_spookyhash_hash128_c_SOURCES =
# tests_try_spookyhash_hash128_c_SOURCES += tests/try-spookyhash_hash128-c.c
# tests_try_spookyhash_hash128_c_SOURCES += tests/try-spookyhash-common-c.h
# tests_try_spookyhash_hash128_c_DEPENDENCIES =
# tests_try_spookyhash_hash128_c_DEPENDENCIES += libats2-spookyhash.la
# tests_try_spookyhash_hash128_c_LDADD =
# tests_try_spookyhash_hash128_c_LDADD += libats2-spookyhash.la

# EXTRA_PROGRAMS += tests/try-spookyhash_hash64-c
# CLEANFILES += tests/try-spookyhash_hash64-c
# tests_try_spookyhash_hash64_c_SOURCES =
# tests_try_spookyhash_hash64_c_SOURCES += tests/try-spookyhash_hash64-c.c
# tests_try_spookyhash_hash64_c_SOURCES += tests/try-spookyhash-common-c.h
# tests_try_spookyhash_hash64_c_DEPENDENCIES =
# tests_try_spookyhash_hash64_c_DEPENDENCIES += libats2-spookyhash.la
# tests_try_spookyhash_hash64_c_LDADD =
# tests_try_spookyhash_hash64_c_LDADD += libats2-spookyhash.la

# EXTRA_PROGRAMS += tests/try-spookyhash_hash32-c
# CLEANFILES += tests/try-spookyhash_hash32-c
# tests_try_spookyhash_hash32_c_SOURCES =
# tests_try_spookyhash_hash32_c_SOURCES += tests/try-spookyhash_hash32-c.c
# tests_try_spookyhash_hash32_c_SOURCES += tests/try-spookyhash-common-c.h
# tests_try_spookyhash_hash32_c_DEPENDENCIES =
# tests_try_spookyhash_hash32_c_DEPENDENCIES += libats2-spookyhash.la
# tests_try_spookyhash_hash32_c_LDADD =
# tests_try_spookyhash_hash32_c_LDADD += libats2-spookyhash.la

# EXTRA_PROGRAMS += tests/try-spookyhash-incremental-c
# CLEANFILES += tests/try-spookyhash-incremental-c
# tests_try_spookyhash_incremental_c_SOURCES =
# tests_try_spookyhash_incremental_c_SOURCES += tests/try-spookyhash-incremental-c.c
# tests_try_spookyhash_incremental_c_SOURCES += tests/try-spookyhash-common-c.h
# tests_try_spookyhash_incremental_c_DEPENDENCIES =
# tests_try_spookyhash_incremental_c_DEPENDENCIES += libats2-spookyhash.la
# tests_try_spookyhash_incremental_c_LDADD =
# tests_try_spookyhash_incremental_c_LDADD += libats2-spookyhash.la

# EXTRA_PROGRAMS += tests/try-spookyhash_hash128-c-misaligned
# CLEANFILES += tests/try-spookyhash_hash128-c-misaligned
# tests_try_spookyhash_hash128_c_misaligned_SOURCES =
# tests_try_spookyhash_hash128_c_misaligned_SOURCES += tests/try-spookyhash_hash128-c-misaligned.c
# tests_try_spookyhash_hash128_c_misaligned_SOURCES += tests/try-spookyhash-common-c.h
# tests_try_spookyhash_hash128_c_misaligned_DEPENDENCIES =
# tests_try_spookyhash_hash128_c_misaligned_DEPENDENCIES += libats2-spookyhash.la
# tests_try_spookyhash_hash128_c_misaligned_LDADD =
# tests_try_spookyhash_hash128_c_misaligned_LDADD += libats2-spookyhash.la

# if WRITE_REFERENCE_DATA

# $(srcdir)/tests/reference-for-seeds-eq-zero.dat: \
# 				tests/compute-reference-for-seeds-eq-zero.sh \
# 				tests/compute-reference-result
# # If the srcdir is unwritable, do not try to write over the test
# # data. This will be the case during a ‘make distcheck’.
# 	if test -w $(@D) ; then $(<) > $(@) ; else : ; fi

# $(srcdir)/tests/reference-for-hash128-seed.dat: \
# 				tests/compute-reference-for-hash128-seed.sh \
# 				tests/compute-reference-result
# # If the srcdir is unwritable, do not try to write over the test
# # data. This will be the case during a ‘make distcheck’.
# 	if test -w $(@D) ; then $(<) > $(@) ; else : ; fi

# $(srcdir)/tests/reference-for-hash64-seed.dat: \
# 				tests/compute-reference-for-hash64-seed.sh \
# 				tests/compute-reference-result
# # If the srcdir is unwritable, do not try to write over the test
# # data. This will be the case during a ‘make distcheck’.
# 	if test -w $(@D) ; then $(<) > $(@) ; else : ; fi

# $(srcdir)/tests/reference-for-hash32-seed.dat: \
# 				tests/compute-reference-for-hash32-seed.sh \
# 				tests/compute-reference-result
# # If the srcdir is unwritable, do not try to write over the test
# # data. This will be the case during a ‘make distcheck’.
# 	if test -w $(@D) ; then $(<) > $(@) ; else : ; fi

# endif WRITE_REFERENCE_DATA

# TESTS =

# TESTS += tests/test-spookyhash_hash128-for-seeds-eq-zero.sh
# TESTS += tests/test-spookyhash_hash64-for-seeds-eq-zero.sh
# TESTS += tests/test-spookyhash_hash32-for-seeds-eq-zero.sh
# TESTS += tests/test-spookyhash-incremental-for-seeds-eq-zero.sh
# TESTS += tests/test-spookyhash_hash128-misaligned-for-seeds-eq-zero.sh

# TESTS += tests/test-spookyhash_hash128-for-hash128-seed.sh
# TESTS += tests/test-spookyhash-incremental-for-hash128-seed.sh
# TESTS += tests/test-spookyhash_hash128-misaligned-for-hash128-seed.sh

# TESTS += tests/test-spookyhash_hash128-for-hash64-seed.sh
# TESTS += tests/test-spookyhash_hash64-for-hash64-seed.sh
# TESTS += tests/test-spookyhash-incremental-for-hash64-seed.sh
# TESTS += tests/test-spookyhash_hash128-misaligned-for-hash64-seed.sh

# TESTS += tests/test-spookyhash_hash128-for-hash32-seed.sh
# TESTS += tests/test-spookyhash_hash64-for-hash32-seed.sh
# TESTS += tests/test-spookyhash_hash32-for-hash32-seed.sh
# TESTS += tests/test-spookyhash-incremental-for-hash32-seed.sh
# TESTS += tests/test-spookyhash_hash128-misaligned-for-hash32-seed.sh

# TESTS += tests/test-spookyhash_hash128-c-for-seeds-eq-zero.sh
# TESTS += tests/test-spookyhash_hash64-c-for-seeds-eq-zero.sh
# TESTS += tests/test-spookyhash_hash32-c-for-seeds-eq-zero.sh
# TESTS += tests/test-spookyhash-incremental-c-for-seeds-eq-zero.sh
# TESTS += tests/test-spookyhash_hash128-c-misaligned-for-seeds-eq-zero.sh

# TESTS += tests/test-spookyhash_hash128-c-for-hash128-seed.sh
# TESTS += tests/test-spookyhash-incremental-c-for-hash128-seed.sh
# TESTS += tests/test-spookyhash_hash128-c-misaligned-for-hash128-seed.sh

# TESTS += tests/test-spookyhash_hash128-c-for-hash64-seed.sh
# TESTS += tests/test-spookyhash_hash64-c-for-hash64-seed.sh
# TESTS += tests/test-spookyhash-incremental-c-for-hash64-seed.sh
# TESTS += tests/test-spookyhash_hash128-c-misaligned-for-hash64-seed.sh

# TESTS += tests/test-spookyhash_hash128-c-for-hash32-seed.sh
# TESTS += tests/test-spookyhash_hash64-c-for-hash32-seed.sh
# TESTS += tests/test-spookyhash_hash32-c-for-hash32-seed.sh
# TESTS += tests/test-spookyhash-incremental-c-for-hash32-seed.sh
# TESTS += tests/test-spookyhash_hash128-c-misaligned-for-hash32-seed.sh

# $(TESTS): $(srcdir)/tests/reference-for-seeds-eq-zero.dat
# $(TESTS): $(srcdir)/tests/reference-for-hash128-seed.dat
# $(TESTS): $(srcdir)/tests/reference-for-hash64-seed.dat
# $(TESTS): $(srcdir)/tests/reference-for-hash32-seed.dat
# $(TESTS): tests/try-spookyhash_hash128
# $(TESTS): tests/test-spookyhash_hash128.sh
# $(TESTS): tests/try-spookyhash_hash64
# $(TESTS): tests/test-spookyhash_hash64.sh
# $(TESTS): tests/try-spookyhash_hash32
# $(TESTS): tests/test-spookyhash_hash32.sh
# $(TESTS): tests/try-spookyhash-incremental
# $(TESTS): tests/test-spookyhash-incremental.sh
# $(TESTS): tests/try-spookyhash_hash128-misaligned
# $(TESTS): tests/test-spookyhash_hash128-misaligned.sh
# $(TESTS): tests/try-spookyhash_hash128-c
# $(TESTS): tests/test-spookyhash_hash128-c.sh
# $(TESTS): tests/try-spookyhash_hash64-c
# $(TESTS): tests/test-spookyhash_hash64-c.sh
# $(TESTS): tests/try-spookyhash_hash32-c
# $(TESTS): tests/test-spookyhash_hash32-c.sh
# $(TESTS): tests/try-spookyhash-incremental-c
# $(TESTS): tests/test-spookyhash-incremental-c.sh
# $(TESTS): tests/try-spookyhash_hash128-c-misaligned
# $(TESTS): tests/test-spookyhash_hash128-c-misaligned.sh

# tests/test-spookyhash_hash128.sh: tests/test-spookyhash.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@TRY@|tests/try-spookyhash_hash128|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash64.sh: tests/test-spookyhash.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@TRY@|tests/try-spookyhash_hash64|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash32.sh: tests/test-spookyhash.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@TRY@|tests/try-spookyhash_hash32|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash-incremental.sh: tests/test-spookyhash.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@TRY@|tests/try-spookyhash-incremental|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash128-misaligned.sh: tests/test-spookyhash.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@TRY@|tests/try-spookyhash_hash128-misaligned|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash128-c.sh: tests/test-spookyhash.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@TRY@|tests/try-spookyhash_hash128-c|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash64-c.sh: tests/test-spookyhash.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@TRY@|tests/try-spookyhash_hash64-c|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash32-c.sh: tests/test-spookyhash.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@TRY@|tests/try-spookyhash_hash32-c|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash-incremental-c.sh: tests/test-spookyhash.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@TRY@|tests/try-spookyhash-incremental-c|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash128-c-misaligned.sh: tests/test-spookyhash.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@TRY@|tests/try-spookyhash_hash128-c-misaligned|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash128-for-seeds-eq-zero.sh: tests/test-spookyhash-for-seeds-eq-zero.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash128.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash64-for-seeds-eq-zero.sh: tests/test-spookyhash-for-seeds-eq-zero.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash64.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash32-for-seeds-eq-zero.sh: tests/test-spookyhash-for-seeds-eq-zero.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash32.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash-incremental-for-seeds-eq-zero.sh: tests/test-spookyhash-for-seeds-eq-zero.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash-incremental.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash128-misaligned-for-seeds-eq-zero.sh: tests/test-spookyhash-for-seeds-eq-zero.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash128-misaligned.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash128-for-hash32-seed.sh: tests/test-spookyhash-for-hash32-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash128.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash64-for-hash32-seed.sh: tests/test-spookyhash-for-hash32-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash64.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash32-for-hash32-seed.sh: tests/test-spookyhash-for-hash32-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash32.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash-incremental-for-hash32-seed.sh: tests/test-spookyhash-for-hash32-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash-incremental.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash128-misaligned-for-hash32-seed.sh: tests/test-spookyhash-for-hash32-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash128-misaligned.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash128-for-hash64-seed.sh: tests/test-spookyhash-for-hash64-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash128.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash64-for-hash64-seed.sh: tests/test-spookyhash-for-hash64-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash64.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash-incremental-for-hash64-seed.sh: tests/test-spookyhash-for-hash64-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash-incremental.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash128-misaligned-for-hash64-seed.sh: tests/test-spookyhash-for-hash64-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash128-misaligned.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash128-for-hash128-seed.sh: tests/test-spookyhash-for-hash128-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash128.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash-incremental-for-hash128-seed.sh: tests/test-spookyhash-for-hash128-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash-incremental.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash128-misaligned-for-hash128-seed.sh: tests/test-spookyhash-for-hash128-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash128-misaligned.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash128-c-for-seeds-eq-zero.sh: tests/test-spookyhash-for-seeds-eq-zero.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash128-c.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash64-c-for-seeds-eq-zero.sh: tests/test-spookyhash-for-seeds-eq-zero.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash64-c.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash32-c-for-seeds-eq-zero.sh: tests/test-spookyhash-for-seeds-eq-zero.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash32-c.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash-incremental-c-for-seeds-eq-zero.sh: tests/test-spookyhash-for-seeds-eq-zero.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash-incremental-c.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash128-c-misaligned-for-seeds-eq-zero.sh: tests/test-spookyhash-for-seeds-eq-zero.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash128-c-misaligned.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash128-c-for-hash32-seed.sh: tests/test-spookyhash-for-hash32-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash128-c.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash64-c-for-hash32-seed.sh: tests/test-spookyhash-for-hash32-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash64-c.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash32-c-for-hash32-seed.sh: tests/test-spookyhash-for-hash32-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash32-c.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash-incremental-c-for-hash32-seed.sh: tests/test-spookyhash-for-hash32-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash-incremental-c.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash128-c-misaligned-for-hash32-seed.sh: tests/test-spookyhash-for-hash32-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash128-c-misaligned.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash128-c-for-hash64-seed.sh: tests/test-spookyhash-for-hash64-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash128-c.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash64-c-for-hash64-seed.sh: tests/test-spookyhash-for-hash64-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash64-c.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash-incremental-c-for-hash64-seed.sh: tests/test-spookyhash-for-hash64-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash-incremental-c.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash128-c-misaligned-for-hash64-seed.sh: tests/test-spookyhash-for-hash64-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash128-c-misaligned.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash128-c-for-hash128-seed.sh: tests/test-spookyhash-for-hash128-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash128-c.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash-incremental-c-for-hash128-seed.sh: tests/test-spookyhash-for-hash128-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash-incremental-c.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# tests/test-spookyhash_hash128-c-misaligned-for-hash128-seed.sh: tests/test-spookyhash-for-hash128-seed.sh.in GNUmakefile
# 	$(call v,GEN)$(SED) -e 's|@''POSIX_SH@|$(POSIX_SH)|g' \
# 			-e 's|@''abs_top_srcdir@|$(abs_top_srcdir)|g' \
# 			-e 's|@TEST_SH@|tests/test-spookyhash_hash128-c-misaligned.sh|g' \
# 			$(<) > $(@) && chmod +x $(@)

# EXTRA_DIST += tests/test-spookyhash.sh.in
# EXTRA_DIST += tests/test-spookyhash-for-seeds-eq-zero.sh.in
# EXTRA_DIST += tests/test-spookyhash-for-hash128-seed.sh.in
# EXTRA_DIST += tests/test-spookyhash-for-hash64-seed.sh.in
# EXTRA_DIST += tests/test-spookyhash-for-hash32-seed.sh.in

# tests-clean:
# 	-rm -f tests/*.$(OBJEXT)
# 	-rm -f tests/*.sh

#--------------------------------------------------------------------------
#
# Computation of dependencies.
#

EXTRA_PROGRAMS += list-ats-dependencies
EXTRA_DIST += list-ats-dependencies.dats
CLEANFILES += list-ats-dependencies
CLEANFILES += list-ats-dependencies_depsprog.c

nodist_list_ats_dependencies_SOURCES =
nodist_list_ats_dependencies_SOURCES += list-ats-dependencies_depsprog.c
list_ats_dependencies_CPPFLAGS =
list_ats_dependencies_CPPFLAGS += $(AM_CPPFLAGS)
list_ats_dependencies_CPPFLAGS += -DATS_MEMALLOC_LIBC
list_ats_dependencies_DEPENDENCIES =
list_ats_dependencies_DEPENDENCIES += list-ats-dependencies.dats
list_ats_dependencies_LDADD =
list_ats_dependencies_LDADD += -L'$(PATSHOME)/ccomp/atslib/lib'
list_ats_dependencies_LDADD += -latslib

#--------------------------------------------------------------------------

# nodist_pkgconfig_DATA += ats2-spookyhash.pc
# nodist_pkgconfig_DATA += spookyhash.pc

#--------------------------------------------------------------------------

# EXTRA_DIST += reference-implementation/SpookyV2.cpp
# EXTRA_DIST += reference-implementation/SpookyV2.h
# EXTRA_DIST += reference-implementation/TestSpookyV2.cpp

#--------------------------------------------------------------------------
# local variables:
# coding: utf-8
# end:
