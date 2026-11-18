COVERAGE=cargo llvm-cov --doctests
coverage:
	@$(COVERAGE) | bat --wrap=never

coverage-html:
	@$(COVERAGE) --open

coverage-diff:
	@$(COVERAGE) --text --color=always

.PHONY: web web-serve
web:
	wasm-pack build web --target web --release --out-dir www/pkg --no-typescript

web-serve: web
	python -m http.server -d web/www 8000
