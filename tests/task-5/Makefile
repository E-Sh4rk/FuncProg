.PHONY: all clean

JOUJOU=../../joujou

all:
	cp ../../category.ml .
	cp ../../tiny_mlp.j .
	cp ../../tiny_mlp_test.ml .
	./test.sh tiny_mlp

clean:
	rm -f *.cmo *.cmx *.cmi *.o tiny_mlp.j tiny_mlp.ml tiny_mlp_test.ml category.ml *~ *.log *_test
