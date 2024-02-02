from lib_gen_action import Grammar

grammar_text = """
htmlDocument:

  | vv3
  | vv4
  | vv4 vv3
  | DTD
  | DTD vv3
  | DTD vv4
  | DTD vv4 vv3
  | vv4 vv4
  | vv4 vv4 vv3
  | vv4 DTD
  | vv4 DTD vv3
  | vv4 DTD vv4
  | vv4 DTD vv4 vv3
  | HTML
  | HTML vv3
  | HTML vv4
  | HTML vv4 vv3
  | HTML DTD
  | HTML DTD vv3
  | HTML DTD vv4
  | HTML DTD vv4 vv3
  | HTML vv4 vv4
  | HTML vv4 vv4 vv3
  | HTML vv4 DTD
  | HTML vv4 DTD vv3
  | HTML vv4 DTD vv4
  | HTML vv4 DTD vv4 vv3
  | vv4 vv4 vv4
  | vv4 vv4 vv4 vv3
  | vv4 vv4 DTD
  | vv4 vv4 DTD vv3
  | vv4 vv4 DTD vv4
  | vv4 vv4 DTD vv4 vv3
  | vv4 HTML
  | vv4 HTML vv3
  | vv4 HTML vv4
  | vv4 HTML vv4 vv3
  | vv4 HTML DTD
  | vv4 HTML DTD vv3
  | vv4 HTML DTD vv4
  | vv4 HTML DTD vv4 vv3
  | vv4 HTML vv4 vv4
  | vv4 HTML vv4 vv4 vv3
  | vv4 HTML vv4 DTD
  | vv4 HTML vv4 DTD vv3
  | vv4 HTML vv4 DTD vv4
  | vv4 HTML vv4 DTD vv4 vv3 ;
vv4:
    scriptletOrSeaWs vv4
  | scriptletOrSeaWs ;
vv3:
    htmlElements vv3
  | htmlElements ;
scriptletOrSeaWs:
    SCRIPTLET
  | SEA_WS ;
htmlElements:
    htmlElement
  | htmlElement vv2
  | vv2 htmlElement
  | vv2 htmlElement vv2 ;
vv2:
    htmlMisc vv2
  | htmlMisc ;
htmlElement:
    <TAG_OPEN_h1  TAG_CLOSE_h1>
  | <TAG_OPEN_h1 vv1 TAG_CLOSE_h1>
  | <TAG_OPEN_h2  TAG_CLOSE_h2>
  | <TAG_OPEN_h2 vv1 TAG_CLOSE_h2>
  | <TAG_OPEN_h3  TAG_CLOSE_h3>
  | <TAG_OPEN_h3 vv1 TAG_CLOSE_h3>
  | <TAG_OPEN_h4  TAG_CLOSE_h4>
  | <TAG_OPEN_h4 vv1 TAG_CLOSE_h4>
  | <TAG_OPEN_div  TAG_CLOSE_div>
  | <TAG_OPEN_div vv1 TAG_CLOSE_div>
  | <TAG_OPEN_b  TAG_CLOSE_b>
  | <TAG_OPEN_b vv1 TAG_CLOSE_b>
  | <TAG_OPEN_i  TAG_CLOSE_i>
  | <TAG_OPEN_i vv1 TAG_CLOSE_i>
  | <TAG_OPEN_ul  TAG_CLOSE_ul>
  | <TAG_OPEN_ul vv1 TAG_CLOSE_ul>
  | <TAG_OPEN_ol  TAG_CLOSE_ol>
  | <TAG_OPEN_ol vv1 TAG_CLOSE_ol>
  | <TAG_OPEN_table  TAG_CLOSE_table>
  | <TAG_OPEN_table vv1 TAG_CLOSE_table>
  | TAG_OPEN
  | TAG_CLOSE
  | TAG_SCLOSE
  | CDATA
  | SCRIPTLET
  | htmlChardata
  | htmlComment
  | script
  | style ;
vv1:
    htmlElement vv1
  | htmlElement ;
htmlChardata:
    HTML_TEXT
  | SEA_WS ;
htmlMisc:
    htmlComment
  | SEA_WS ;
htmlComment:
    HTML_COMMENT
  | HTML_CONDITIONAL_COMMENT ;
script:
    SCRIPT_OPEN SCRIPT_BODY
  | SCRIPT_OPEN SCRIPT_SHORT_BODY ;
style:
    STYLE_OPEN STYLE_BODY
  | STYLE_OPEN STYLE_SHORT_BODY ;"""

g = Grammar(grammar_text)

with open("tree_action_{}.ml".format("html"), "w") as f:
    f.write(g.show_parse_tree_action())
    f.write(g.show_run_ppda())
    f.write(g.show_run_epda_no_act())
    f.write(g.show_stack_action())
    f.write(g.show_run_epda_act())