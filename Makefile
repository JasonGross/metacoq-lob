.DEFAULT_GOAL := all

SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)

ifneq ($(wildcard .git),)
FILE_FINDER := git ls-files
else
$(warning Not a git clone, using find instead)
FILE_FINDER := find -name
endif

WARNINGS := +implicit-core-hint-db,+implicits-in-term,+non-reversible-notation,+deprecated-intros-until-0,+deprecated-focus,+unused-intro-pattern,+deprecated-hint-constr,+fragile-hint-constr,+variable-collision,+unexpected-implicit-declaration,+omega-is-deprecated,+deprecated-instantiate-syntax,+non-recursive,+deprecated-hint-rewrite-without-locality,+deprecated-hint-without-locality,+deprecated-instance-without-locality,+undeclared-scope,+deprecated-typeclasses-transparency-without-locality,+future-coercion-class-field

_CoqProject::
	$(HIDE)(echo "-R theories MetaCoq.Lob"; echo '-arg -w -arg $(WARNINGS)'; ($(FILE_FINDER) "*.v")) > $@

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@

%: Makefile.coq
	$(MAKE) -f Makefile.coq $@
