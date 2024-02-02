from lib_gen_action import Grammar

grammar_text = """
json:
    value ;
obj:
    <'{' vv2 '}'>
  | <'{'     '}'> ;
vv2:
    pair vv4
  | pair ;
vv4:
    ',' pair
  | ',' pair vv4 ;
pair:
    STRING ':' value ;
arr:
    <'[' vv1 ']'>
  | <'['     ']'> ;
vv1:
    value vv3
  | value ;
vv3:
    ',' value
  | ',' value vv3 ;
value:
    STRING
  | NUMBER
  | obj
  | arr
  | 'true'
  | 'false'
  | 'null' ;"""

g = Grammar(grammar_text)

with open("tree_action_{}.ml".format("json"), "w") as f:
    f.write(g.show_parse_tree_action())
    f.write(g.show_run_ppda())
    f.write(g.show_run_epda_no_act())
    f.write(g.show_stack_action())
    f.write(g.show_run_epda_act())