from lib_gen_action import Grammar

grammar_text = """
document:
    element
  | element vv3
  | vv3 element
  | vv3 element vv3
  | prolog element
  | prolog element vv3
  | prolog vv3 element
  | prolog vv3 element vv3 ;
vv3:
    misc vv3
  | misc ;
prolog:
    XMLDeclOpen SPECIAL_CLOSE
  | XMLDeclOpen vv2 SPECIAL_CLOSE ;
vv2:
    attribute vv2
  | attribute ;
content:

  | vv1
  | chardata
  | chardata vv1 ;
vv1:
    COMMENT chardata vv1
  | COMMENT vv1
  | PI chardata vv1
  | PI vv1
  | CDATA chardata vv1
  | CDATA vv1
  | reference chardata vv1
  | reference vv1
  | element chardata vv1
  | element vv1
  | COMMENT chardata
  | COMMENT
  | PI chardata
  | PI
  | CDATA chardata
  | CDATA
  | reference chardata
  | reference
  | element chardata
  | element ;
element:
    <TAG_OPEN content TAG_CLOSE>
  | TAG_SCLOSE ;
reference:
    EntityRef
  | CharRef ;
attribute:
    Name '=' STRING ;
chardata:
    TEXT
  | SEA_WS ;
misc:
    COMMENT
  | PI
  | SEA_WS ;"""

g = Grammar(grammar_text)

with open("tree_action_{}.ml".format("xml"), "w") as f:
    f.write(g.show_parse_tree_action())
    f.write(g.show_run_ppda())
    f.write(g.show_run_epda_no_act())
    f.write(g.show_stack_action())
    f.write(g.show_run_epda_act())