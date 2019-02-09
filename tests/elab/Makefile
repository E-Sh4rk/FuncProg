.PHONY: all clean

JOUJOU=../../joujou --typecheck

GOODS = $(wildcard *-good.j)
BADS  = $(wildcard *-bad.j)

all:
	@ echo '* Bonus Task: Writing an elaborator' | tee elab.log
	@for good in $(GOODS); do \
	  ($(JOUJOU) $$good && echo "  - [OK] $$good") || echo "  - [KO] $$good"; \
	done | tee -a elab.log

	@for bad in $(BADS); do \
	  ($(JOUJOU) $$bad 2> $$bad.log && echo "  - [KO] $$bad") \
          || echo "  - [XFAIL] $$bad"; \
	  cat $$bad.log; \
	done | tee -a elab.log

	@ echo '** Score for this task:' \
        `grep '\[OK\]\|\[XFAIL\]' elab.log | wc -l`/\
	`grep '^  -' elab.log | wc -l | tr -d ' '`

clean:
	rm -f *~ *.log
