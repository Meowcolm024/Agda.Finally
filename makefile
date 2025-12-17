all: build

agda:
	cd src && \
	agda --html \
	--html-dir=../tmp \
	--css="./static/Agda.css" \
	--html-highlight=auto \
	finally.lagda.md

build: agda
	node build.js

serve:
	python3 -m http.server -d docs

clean:
	rm -r tmp docs