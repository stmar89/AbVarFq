# usage:
# make all	    	# cleans up old file and makes a new one

.PHONY : clean_old 	# prevent errors from rm

input = ../spec
outfile = ./ListOfCommands.md

all: clean_old magma_script

clean_old:
	@echo "Removing old ListOfCommands.md..."
	-rm ${outfil}
	@echo "...Done"

magma_script:
	@echo "Printing the new ListOfCommands.md."
	@echo "The commands will be sorted in the same way as they are listed in the spec file"
	magma -b input:=${input} output_file:=${outfile} magma_make_list_of_func.txt
	@echo "...Done"
	@echo "...Don't forget to push the new changes!"
