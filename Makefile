SCALAC    := fsc
SCALA_RUN := scala
OUT_CLASS := qmm

.PHONY: all clean run scrun

%.class: %.scala
	$(SCALAC) $<

all: main.class

clean:
	@rm -rf *.class

scrun:
	$(SCALA_RUN) main.scala
	
run: main.class
	@$(SCALA_RUN) $(OUT_CLASS)

