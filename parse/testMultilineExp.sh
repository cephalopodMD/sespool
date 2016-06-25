../cool --lex test/multilineExp.cl
../cool --parse test/multilineExp.cl --out test/multilineExpRef
python2.6 main.py test/multilineExp.cl-lex
