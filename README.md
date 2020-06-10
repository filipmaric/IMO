# IMO
Formalization of IMO solutions in Isabelle/HOL

Step 0: (only once)

Folder IMO_files is made using Isabelle command:
$ISABELLE_HOME/bin/isabelle mkroot IMO_files

Step 1:

The basic tex file for storing relevant information about the generated document:
IMO_files/document/root.tex 

Step 2:

Adding a new theory file in the folder...
Must be added in the ROOT file

Step 3:

A pdf file is generated using Isabelle command:
$ISABELLE_HOME/bin/isabelle build -D IMO_files

and it is located at:
IMO_files/output/document.pdf
