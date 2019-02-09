.PHONY: all clean

JOUJOU_EE=../../joujou --no-elaboration --eta-expanse
JOUJOU=../../joujou --no-elaboration --typecheck

GOODS = $(wildcard *-good.j)
GOODS_ETA = $(wildcard *-eta-good.j)
BADS  = $(wildcard *-bad.j)

all:
	@ echo '* Task 2: Writing a typechecker' | tee task-2.log
	@for good in $(GOODS); do \
	  ($(JOUJOU) $$good && echo "  - [OK] $$good") || echo "  - [KO] $$good"; \
	done | tee -a task-2.log

	@for good in $(GOODS_ETA); do \
	  ($(JOUJOU_EE) $$good && echo "  - [OK] $$good") || echo "  - [KO] $$good"; \
	done | tee -a task-2.log

	@for bad in $(BADS); do \
	  ($(JOUJOU_EE) $$bad 2> $$bad.log && echo "  - [KO] $$bad") \
          || echo "  - [XFAIL] $$bad"; \
	  cat $$bad.log; \
	done | tee -a task-2.log

	@ echo '** Score for this task:' \
        `grep '\[OK\]\|\[XFAIL\]' task-2.log | wc -l`/\
	`grep '^  -' task-2.log | wc -l | tr -d ' '`

clean:
	rm -f *~ *.log
