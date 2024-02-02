class Grammar:
    rules: list[tuple[str, list[str]]]
    grammar: dict[str, list[str]]
    tokens: list[tuple[int, str]]
    call_syms: list[str]
    ret_syms: list[str]
    plain_syms: list[str]

    def __init__(self, grammar_text: str):
        self.gen_grammar(grammar_text)
        self.gen_tokens()

    def gen_grammar(self, grammar_text: str):
        grammar = {}
        for rules in grammar_text.split(";"):
            if rules:
                nt, alts = rules.split(":", 1)
                nt = nt.strip()
                alts = alts.split("|")
                alts = [[alt.strip() for alt in r.split(" ")] for r in alts]
                alts = [[alt for alt in r if alt] for r in alts]
                grammar[nt] = alts

        self.grammar = grammar
        self.rules = [(nt, alt) for nt in grammar for alt in grammar[nt]]

    def gen_tokens(self):
        call_syms = []
        ret_syms = []
        plain_syms = []
        for (_, alt) in self.rules:
            for term in alt:
                if (term[0] == "'" or term[0].isupper() or term[0] == "<"):
                    if term[0] == "<":
                        term = term[1:]
                        if term not in call_syms:
                            call_syms.append(term)
                    elif term[-1] == ">":
                        term = term[:-1]
                        if term not in ret_syms:
                            ret_syms.append(term)
                    elif term not in plain_syms:
                        plain_syms.append(term)

        self.call_syms = call_syms
        self.ret_syms = ret_syms
        self.plain_syms = plain_syms
        self.tokens = list(enumerate(plain_syms+call_syms+ret_syms))

    def show_parse_tree_action(self,):
        prog: list[str] = []

        # NOTE - header
        prog.append("open Core")
        prog.append("open TCFGParser.Utils")
        prog.append("open TCFGParser.TCFGParseTree")
        prog.append("")

        # NOTE - nontemrinal type
        prog.append("type nt =")
        for nt in self.grammar:
            prog.append(" | S_{}".format(nt))
        prog.append("[@@deriving show]")
        prog.append("")

        # NOTE - terminal type
        prog.append("type tn =")
        for t in self.tokens:
            prog.append(" | S_{} (* {} *)".format(t[0], t[1]))
        prog.append("[@@deriving show]")
        prog.append("")

        # NOTE - parse tree type
        prog.append("""type parse_tree ="""
        """\n | Node of (nt * parse_tree array)"""
        """\n | Leaf of (tn * string)"""
        """\n | PTNull""")
        prog.append("[@@deriving show]")
        prog.append("")

        # NOTE - restore the leaves
        prog.append("let restore_leaves w tokens =")
        prog.append("  List.zip_exn w tokens")
        prog.append("  |> List.map ~f:(fun (lexeme, name) ->")
        prog.append("  match name with")
        for token in self.tokens:
            prog.append(
                "  | \"{}\" -> Leaf (S_{}, lexeme)".format(token[1], token[0]))
        prog.append("  | s -> err (sprintf \"invalid token name %s\" s))")
        prog.append("")

        prog.append("let act get_stack_value pop_stack_value i_rule =")
        prog.append("  match i_rule with")
        for i, (nt, alt) in enumerate(self.rules):
            prog.append(
                "  | {} ->\n    {}".format(i, self.show_alt_action(i, nt, alt))
            )
        prog.append("  | _ -> err \" action not found \"")
        prog.append("")

        return "\n".join(prog)

    def show_run_ppda(self):
        prog: list[str] = []
        # NOTE - run parser PDA
        prog.append("let run_ppda lookup_pda2 lookup_pda3 hint forest : unit =")
        prog.append("  let me = ref 1 in")
        prog.append("  let st = ref [] in")
        prog.append("  for l = 0 to Array.length hint - 1 do")
        prog.append("    match hint.(l) with")
        for i, (_, token) in enumerate(self.tokens):
            if token in self.call_syms:
                prog.append("""         | {} -> (* {} *)
                    st := !me :: !st;
                    me := lookup_pda2 (!me, {});
                    forest.(l) <- !me""".format(i, token, i))
            elif token in self.ret_syms:
                prog.append("""         | {} -> (* {} *)
                    me := lookup_pda3 (!me, hdi !st, {});
                    forest.(l) <- !me;
                    st := tl !st""".format(i, token, i))
        prog.append("""         | i ->
            me := lookup_pda2 (!me, i);
            forest.(l) <- !me""")
        prog.append("       done")
        prog.append("")

        return "\n".join(prog)

    def show_alt_action(self, _, nt, alt):
        prog_create_children = "let children = Array.init {} ~f:(fun i -> get_stack_value i) in".format(
            len(alt))
        prog_pop_value = "pop_stack_value {};".format(len(alt))
        prog_assign = "let node = Node(S_{}, children) in".format(nt)
        prog_return_value = "node"

        prog = [prog_create_children, prog_pop_value,
                prog_assign, prog_return_value]

        return "( {} )".format(("\n"+" "*6).join(prog))

    def show_run_epda_no_act(self,):
        main_prog = """let run_epda_no_act lookup_eTrans lookup_epda (m : int array) (hint : int array) =
        let re, irules = lookup_eTrans m.(Array.length hint - 1) in
        if re = 0 then err "Extraction Error: Cannot terminate.";
        let stack =
            ref
            (match hint.(Array.length hint - 1) with
            {})
        in
        if Int.equal (Array.length hint - 1) 0 then ()
        else
            let r = ref re in
            for i = Array.length hint - 2 downto 0 do
            let r', irules = lookup_epda (!r, hdi !stack, m.(i)) in
            r := r';
            stack :=
                match hint.(i) with
                {}
            done

        """

        prog_ini_stack = []
        for i, (_,token) in enumerate(self.tokens):
            if token in self.ret_syms:
                prog_ini_stack.append("""        | {} -> [ re ]""".format(i))
        prog_ini_stack.append("""        | _ ->  []""")

        prog_ini_stack = "\n".join(prog_ini_stack)

        prog_stack = []
        for i, (_,token) in enumerate(self.tokens):
            if token in self.call_syms:
                prog_stack.append("""        | {} -> tl !stack""".format(i))
            elif token in self.ret_syms:
                prog_stack.append("""        | {} -> !r :: !stack""".format(i))
        prog_stack.append("""        | _ -> !stack""")
        prog_stack = "\n".join(prog_stack)


        return main_prog.format(prog_ini_stack, prog_stack)

    def show_stack_action(self):
        return """
let run_action w (actions : int list array) =
let stack_height = ref 16 in
let value_stack = ref (Array.create ~len:!stack_height PTNull) in
let stack_top = ref (-1) in
let push_stack v =
stack_top := !stack_top + 1;
if !stack_top >= !stack_height then (
    let new_height = !stack_height * 2 in
    let new_value_stack = Array.create ~len:new_height PTNull in
    Array.blit ~src:!value_stack ~src_pos:0 ~dst:new_value_stack ~dst_pos:0
    ~len:!stack_height;
    stack_height := new_height;
    value_stack := new_value_stack);
!value_stack.(!stack_top) <- v
in
let get_stack_value i = !value_stack.(!stack_top - i) in
let pop_stack_value k = stack_top := !stack_top - k in
let run_act acts =
List.iter acts ~f:(fun a ->
    let node = act get_stack_value pop_stack_value a in
    push_stack node)
in
for l = 0 to Array.length w - 1 do
push_stack w.(l);
let acts = actions.(l) in
run_act acts
done;
assert (Int.equal !stack_top 0);
!value_stack.(0)

let stack_height = ref 16
let value_stack : (parse_tree array) ref = ref (Array.create ~len:!stack_height PTNull) 
let stack_top = ref (-1) 
let push_stack v =
stack_top := !stack_top + 1;
if !stack_top >= !stack_height then (
    (* NOTE - enlarge the stack *)
    let new_height = !stack_height * 2 in
    let new_value_stack = Array.create ~len:new_height PTNull in
    Array.blit ~src:!value_stack ~src_pos:0 ~dst:new_value_stack
    ~dst_pos:0 ~len:!stack_height;
    stack_height := new_height;
    value_stack := new_value_stack);
!value_stack.(!stack_top) <- v

let get_stack_value i = !value_stack.(!stack_top - i)
let pop_stack_value k = stack_top := !stack_top - k 

let run_action (acts : t_action) =
    Array.iter acts ~f:(fun a ->
        let node = act get_stack_value pop_stack_value a in
        push_stack node)
    
    """


    def show_run_epda_act(self,):
        main_prog = """let run_epda_act lookup_eTrans lookup_epda (forest : int array) (hint : int array) leaves : parse_tree
        =
      stack_top := -1;
      let i = Array.length hint - 1 in
      let re, irules = lookup_eTrans forest.(i) in
      push_stack leaves.(i);
      run_action irules;
      if re = 0 then err "Extraction Error: Cannot terminate.";
      let stack =
        ref
          (match hint.(i) with
          {})
      in
      (if Int.equal i 0 then ()
      else
        let r = ref re in
        for i = Array.length hint - 2 downto 0 do
          let r', irules = lookup_epda (!r, hdi !stack, forest.(i)) in
          push_stack leaves.(i);
          run_action irules;
          r := r';
          stack :=
            match hint.(i) with
            {}
        done);
      assert (Int.equal !stack_top 0);
      !value_stack.(0)
      
      """

        prog_ini_stack = []
        for i, (_,token) in enumerate(self.tokens):
            if token in self.ret_syms:
                prog_ini_stack.append("""        | {} -> [ re ]""".format(i))
        prog_ini_stack.append("""        | _ ->  []""")

        prog_ini_stack = "\n".join(prog_ini_stack)

        prog_stack = []
        for i, (_,token) in enumerate(self.tokens):
            if token in self.call_syms:
                prog_stack.append("""        | {} -> tl !stack""".format(i))
            elif token in self.ret_syms:
                prog_stack.append("""        | {} -> !r :: !stack""".format(i))
        prog_stack.append("""        | _ -> !stack""")
        prog_stack = "\n".join(prog_stack)


        return main_prog.format(prog_ini_stack, prog_stack)