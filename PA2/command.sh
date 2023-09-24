#!/bin/bash

./lexer ./grading/lineno2.cool > my_answer.txt
../../bin/lexer ./grading/lineno2.cool > text_answer.txt
python compare.py