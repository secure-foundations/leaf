# locations in Fail, depends on local file path
/^File/d
# Ltac2 printing changed (https://github.com/coq/coq/pull/18560)
s/StringToIdent\.([a-zA-Z]+) \((.*)\)/StringToIdent.\1 \2/
