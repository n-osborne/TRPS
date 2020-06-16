
html : dir agda/TPRS.lagda.md
	lagda2html agda/TPRS.lagda.md docs/index.html

dir :
	mkdir -p docs
