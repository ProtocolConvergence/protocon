
default: all

CxPfx = ../../cx

tex2web = ../../tex2web/bin/tex2web
man2html = man2html

html/ html/example/ pubhtml/ pubhtml/example/ pubhtml/examplespec/ pubhtml/examplesynt/ pubhtml/examplesoln/:
	mkdir -p $@
	chmod a+rx $@

define webtex_rule
Targets += html/$(1).html
PubTargets += pubhtml/$(1).html

html/$(1).html: webtex/$(1).tex $(2)
	$(tex2web) -x $$< -o $$@ \
		-def examplespec ../../examplespec \
		-def examplesynt ../../examplesynt \
		-def examplesoln ../../examplesoln \
		-def examplesett ../../examplesett
	chmod a+r,a-x $$@

html/$(1).html: | $(dir html/$(1))

pubhtml/$(1).html: webtex/$(1).tex $(2)
	$(tex2web) -x $$< -o $$@ \
		-def examplespec examplespec \
		-def examplesynt examplesynt \
		-def examplesoln examplesoln \
		-def examplesett examplesett
	chmod a+r,a-x $$@

pubhtml/$(1).html: | $(dir pubhtml/$(1))

endef

define example_deps
../examplespec/$(1).prot ../examplesoln/$(1).prot
endef

$(eval \
	$(call webtex_rule,index,webtex/content.tex webtex/changes.tex webtex/thanks.tex) \
	$(call webtex_rule,legit,) \
	$(call webtex_rule,examplelist,) \
	$(call webtex_rule,tut,) \
	$(call webtex_rule,example/ColorRing,$(call example_deps,ColorRing)) \
	$(call webtex_rule,example/MatchRingOneBit,$(call example_deps,MatchRingOneBit)) \
	$(call webtex_rule,example/OrientOddRing,$(call example_deps,OrientOddRing)) \
	$(call webtex_rule,example/TokenRingThreeBit,$(call example_deps,TokenRingThreeBit)) \
	)

define prot_rule
PubTargets += pubhtml/example$(1).prot

pubhtml/example$(1).prot: ../example$(1).prot
	cp -f -T $$< $$@
	chmod a+r,a-x $$@

pubhtml/example$(1).prot: | $(dir pubhtml/example$(1))

endef

$(eval $(foreach f,$(shell cat ../meta/examplespec.files),$(call prot_rule,spec/$(f))))
$(eval $(foreach f,$(shell cat ../meta/examplesynt.files),$(call prot_rule,synt/$(f))))
$(eval $(foreach f,$(shell cat ../meta/examplesoln.files),$(call prot_rule,soln/$(f))))

Targets += html/man.html
PubTargets += pubhtml/man.html

html/man.html pubhtml/man.html: protocon.1
	$(man2html) $< > $@
	chmod a+r,a-x $@

html/man.html: | html

pubhtml/man.html: | pubhtml

all: $(Targets)

pub: $(PubTargets)

.PHONY: clean
clean:
	rm -fr html pubhtml

.PHONY: distclean
distclean: clean
	# Nothing more than a clean.

