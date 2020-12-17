/*
    node:
        ante: [formula]
        succ: [formula]

        left: node
        right: node

 */

class node {
    constructor()
    {
        this.depth = 0;
        this.parent = null;
        this.root = this;
        this.f = [null, null];
        this.Z_pair = null; // null or [const, const']
        this._solved = [null, null];
        this.open = true; // does the branch stop here?
        this.positive = [true, true];
        this.last_ts = [null, null];
        //this.all_used_consts = [[], []]; // just for root: all globally introducted consts (so that we dont reusee some)
        this.used_consts = [[], []]; // all the constants introduced up to this point
        this.inst_consts = []; // only for for-all nodes
        this.used_bridges = []; //list of node pairs (pointers) that have been used for bisim-moves; should be kept both with the R- and Z-nodes
        this.interrupting = false; // for Z/R-nodes coming from the other side

        this.children = [];
    }

    /*clone(new_parent) {
        let n = new_parent  ?  new node()  :  new_parent.offspring();

        n.f = deep_copy(this.f);
        n.Z_pair = deep_copy(this.Z_pair);
        n._solved = this._solved;
        n.open = this.open;
        n.positive = this.positive.slice();
        n.used_consts = [new_parent.used_consts[0].concat(deep_copy(this.used_consts[0])), new_parent.used_consts[1].concat(deep_copy(this.used_consts[1]))]; // krivo prolly
        n.inst_consts = this.inst_consts.slice();
        for (let c of this.children)
            c.clone(n);
        return n;
    }*/

    get_Z() {
        return this.Z_pair;
    }

    get_R(rels = ['R']) {
        if (this.interrupting)
            return null;
        if (this.f[0] && this.positive[0] && rels.includes(this.f[0].rel))
            return [0, this.f[0].rel, this.f[0].vs];
        if (this.f[1] && this.positive[1] && rels.includes(this.f[1].rel))
            return [1, this.f[1].rel, this.f[1].vs];
        return null;
    }

    get_P_or_R() {
        return this.get_R(['P', 'R', 'Q', 'S', 'U', 'V' ]);
    }

    solved() {return (this.f[0] === null || this._solved[0]) && (this.f[1] === null || this._solved[1]) }
    left() {return this.children[0];}
    right() {return this.children[1];}

    text_print(indent) {
        if (!indent) indent = 0;

        return null;
    }

    latex_print(out) {
        return null;
    }

    print() {
        let formula_print =
                i =>
            this.f[i] ?
                (this.interrupting ? `<span style="border: 1px solid black;">` : '') +
                html_str_formula(this.f[i]) +
                ' ' +
                (this.positive[i] ? '⊤' : '⊥') +
                (this.interrupting ? `</span>` : '') +
                ' ' +
                (this._solved[i] ? '✓' : '') :
                '';

        return formula_print(0) + ' · ' + (this.Z_pair ? this.Z_pair[0] + 'Z' +  this.Z_pair[1] : '') + ' · ' + formula_print(1) ; // + "  " + JSON.stringify(this.used_consts);
    }

    html_print() {
        let me = document.createElement('div');
        me.className = 'node';

        let me_html = this.print();
        let form = document.createElement('div');
        form.className = 'text';
        form.innerHTML = me_html;

        me.appendChild(form);

        if (!this.open)
        {
            me.appendChild(document.createTextNode('×'));
        }

        if (!this.children.length) {
            return me;
        }

        let children = document.createElement('div');
        children.className = 'node_children';
        me.appendChild(children);

        if (this.left()) {
            children.appendChild(this.left().html_print());
        }
        if (this.right()) {
            let space = document.createElement('div');
            space.className = 'gentz_as_space';
            children.appendChild(space);
            children.appendChild(this.right().html_print());
        }

        return me;
    }

    offspring(override_ts) {
        let n = new node();
        n.root = this.root;
        n.parent = this;
        n.last_ts = override_ts !== undefined ? override_ts.slice() : this.last_ts.slice();
        n.depth = this.depth + 1;
        //n.bisimilar = this.bisimilar.slice();
        //n.used_consts = [this.used_consts[0].slice(), this.used_consts[1].slice()];
        this.children.push(n);
        return n;
    }

    collect_nodes() {
        let fs = [];
        for (let it = this;  it != null;  it = it.parent)
        {
            fs.push(it);
        }
        return fs;
    }

    collect_unsolved_nodes() {
        let fs = [];
        for (let it = this;  it != null;  it = it.parent)
        {
            if (!it.solved())
                fs.push(it);
        }
        return fs;
    }

    tree_nodes(nodes_list) {
        let initial = nodes_list === undefined;
        if (initial)
        {
            return this.root.tree_nodes([]);
        }

        nodes_list.push(this);
        for (let c of this.children)
            c.tree_nodes(nodes_list);

        return nodes_list;
    }

    alive_above_and_below() {
        let open_leaves = this.open_leaves();
        if (open_leaves.length == 0)
            return new Set();

        let nodes = new Set(this.collect_nodes());

        for (let leave of open_leaves)
            for (let n of leave.collect_nodes())
                nodes.add(n);

        return nodes;
    }

    open_leaves(leave_list) {
        let initial = leave_list === undefined;
        if (initial)
            leave_list = [];

        if (this.children.length == 0) {
            if (this.open)
                leave_list.push(this);
        }
        else
            for (let c of this.children)
                c.open_leaves(leave_list);

        return leave_list;
    }

    active_leaves(leave_list, everything_solved = true) { /* sth not solved AND open */
        let initial = leave_list === undefined;
        if (initial)
            leave_list = [];

        everything_solved = everything_solved && this.solved();

        if (this.children.length == 0) {
            if (this.open &&  !everything_solved)
                leave_list.push(this);
        }
        else
            for (let c of this.children)
                c.active_leaves(leave_list, everything_solved);

        return leave_list;
    }

    choose_side()
    {
        let n = this;
        let side = -1; // left or right? 0/1
        if (n.f[0] && n.f[1] && (n.f[1].op == lall && !n.positive[1] && !n._solved[1] || n._solved[0]))
            side = 1;
        else if (n.f[0])
            side = 0;
        else if (n.f[1])
            side = 1;
        return side;
    }
}

function frm_parse(str)
{
    const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
    parser.feed(str.trim());
    let f = parser.results[0].form;

    let tr = fr => {
        fr.last_ts = 0;
        if (fr.e)
            tr(fr.e);
        if (fr.e1)
            tr(fr.e1);
        if (fr.e2)
            tr(fr.e2);
        return;
    }

    tr(f);

    return f;
}


function s_terms(s /*node*/) /* tuple[rls: seq[string], vars: seq[string]] */
{
    let terms = s.ante.concat(s.succ).map(f => frm_terms(f)).flat();

    terms.sort((a, b) => a[0] == 'e' && b[0] == 'e' ?
        Number.parseInt(a.substring(1)) - Number.parseInt(b.substring(1)) :
        a.localeCompare(b)
    );
    return terms;
}


function axiom(s /*node*/) /*bool*/
{
    return s.ante.some(f => f.op == lfals) ||
        s.succ.some(f => f.op == ltrue) ||
        s.ante.some( f => s.succ.some( g => formulas_eql(f, g) ))
}

var seq_ts = -1;
function get_ts() {
    ++seq_ts;
    return seq_ts;
}

function nodes_contradictory(n, m) {
    if (n.f[0] && m.f[0] && n.positive[0] != m.positive[0] && formulas_eql(n.f[0], m.f[0]))
        return -1;
    if (n.f[1] && m.f[1] && n.positive[1] != m.positive[1] && formulas_eql(n.f[1], m.f[1]))
        return 1;
    return 0;
}

function reg_offspring(l, queue, side, f, pos_f, override_ts, z_part /*, new_used_consts */) {
    if (!f)
        return;

    let n = l.offspring([side === 0 ? override_ts : null, side === 1 ? override_ts : null]);
    n.f = [side === 0 ? f : null, side === 1 ? f : null];
    n.positive = [side === 0 ? pos_f : null, side === 1 ? pos_f : null];
    n.Z_pair = z_part !== "interrupting" ? z_part : null;
    n.interrupting = !!z_part;
    /*if (new_used_consts) {
        n.used_consts[0] = n.used_consts[0].concat(new_used_consts[0]);
        n.used_consts[1] = n.used_consts[1].concat(new_used_consts[1]);
    }*/
    let nodes_above = l.collect_nodes();
    for (let m of nodes_above) /* nodes_above = n.collect_nodes */
    {
        let contr_pos = nodes_contradictory(n, m);
        if (contr_pos) {
            n.open = false;
            n.contradictory_with = m;
            n.contr_pos = contr_pos;
            break;
        }
    }
    if (n.open && queue)
        queue.push(n);
}

function append_to_leaves(root, queue, side,
                          a = {f: undefined, pos: undefined, ts: undefined /*, new_used_consts: undefined*/ },
                          b = {f: undefined, pos: undefined, ts: undefined /*, new_used_consts: undefined*/ },
                          z_part = null
)
{
    let leaves = root.open_leaves();
    for (let l of leaves) {
        reg_offspring(l, queue, side, a.f, a.pos, a.ts, z_part /* a.new_used_consts */)
        reg_offspring(l, queue, side, b.f, b.pos, b.ts, z_part /* a.new_used_consts */ )
    }
}

/* actually, this also does a de morgan for quantifiers, so not just prpo */
function prop_solve(m /* node */) /*bool*/ {
    /* top-down, search for nice rules first */

    let jobbing = true;
    while (jobbing) {
        jobbing = false;

        let q = [m]; /* queue */
        for (let i = 0; i < q.length; ++i) {
            let n = q[i];
            q = q.concat(n.children);

            if (n.solved()) continue;

            let side = n.choose_side();

            let f = n.f[side];

            if (f.rel) {
                n._solved[side] = true;
                jobbing = true;
            }
            if (n.positive[side] && [lnot, land].includes(f.op)) {
                n._solved[side] = true;
                switch (f.op) {
                    case lnot:
                        append_to_leaves(n, q, side, {f: f.e, pos: false});
                        break;
                    case land:
                        append_to_leaves(n, q, side, {f: f.e1, pos: true});
                        append_to_leaves(n, q, side, {f: f.e2, pos: true});
                        break;
                }
                jobbing = true;
            }
            if (!n.positive[side] && [lnot, lor, lcond, lall, lexists].includes(f.op)) {
                n._solved[side] = true;
                switch (f.op) {
                    case lnot:
                        append_to_leaves(n, q, side, {f: f.e, pos: true});
                        break;
                    case lor:
                        append_to_leaves(n, q, side, {f: f.e1, pos: false});
                        append_to_leaves(n, q, side, {f: f.e2, pos: false});
                        break;
                    case lcond:
                        append_to_leaves(n, q, side, {f: f.e1, pos: true});
                        append_to_leaves(n, q, side, {f: f.e2, pos: false});
                        break;
                    case lall:
                        let exi_neg_e = {op: lexists, v: f.v, e: { op: lnot, e: f.e }};
                        append_to_leaves(n, q, side, {f: exi_neg_e, pos: true})
                        break;
                    case lexists:
                        let all_neg_e = {op: lall, v: f.v, e: { op: lnot, e: f.e }};
                        append_to_leaves(n, q, side, {f: all_neg_e, pos: true})
                        break;
                }
                jobbing = true;
            }

        }

        q = [m]; /* queue */
        for (let i = 0; i < q.length; ++i) {
            let n = q[i];
            q = q.concat(n.children);

            if (n.solved()) continue;

            let side = n.choose_side();
            let f = n.f[side];


            if (n.positive[side] && [lor, lcond].includes(f.op)) {
                n._solved[side] = true;
                switch (f.op) {
                    case lor:
                        append_to_leaves(n, q, side, {f: f.e1, pos: true}, {f: f.e2, pos: true});
                        break;
                    case lcond:
                        append_to_leaves(n, q, side, {f: f.e1, pos: false}, {f: f.e2, pos: true});
                        break;
                }
                jobbing = true;
            }
            if (!n.positive[side] && [land].includes(f.op)) {
                n._solved[side] = true;
                switch (f.op) {
                    case land:
                        append_to_leaves(n, q, side, {f: f.e1, pos: false}, {f: f.e2, pos: false});
                        break;
                }
                jobbing = true;
            }
        }
    }

    return;
}

var global_ts = 0;

function make_a_const(a_node, side, is_bisim_move)
{

    let str = (a_node.root.used_consts[side].length + a_node.root.used_consts[1 - side].length).toString();
    let tr;
    if (is_bisim_move)
        tr = a_node.f[1 - side].vs[1].substring(1);
    else
        tr = str;
    let ret = (side === 0 ? "c" : 'd') + tr;

    document.body.appendChild(document.createElement('br'));
    console.log('making a new const: ', ret, a_node, a_node.root.used_consts[0], a_node.root.used_consts[1]);
    document.body.appendChild(a_node.root.html_print());
    document.body.appendChild(document.createElement('br'));

    return ret;
}

window.production = true;

function draw_a_const(c)
{
    if (!c) return '%';
    let str = c.toString();
    let tr = c.substring(1).split('').map(ch => String.fromCharCode(  (window.production ? 0x2080 : '0'.codePointAt(0) )  +  ch.codePointAt(0) - '0'.codePointAt(0) ) );
    return c.substring(0, 1) + tr;
}

function fol_solve(m /* node */) /*bool*/ {

    /* which formula was last instanced? (might use this even for the existential formulas...) */
    let best_node = null;
    let best_node_side = -1;

    let q = [m]; /* queue */
    for (let i = 0; i < q.length; ++i) {
        let n = q[i];
        q = q.concat(n.children);

        if (n.solved()) continue;

        let side = n.choose_side();
        let f = n.f[side];

        if (n.positive[side]) {
            switch (f.op) {
                case lexists:
                    if (!best_node   ||   best_node.f[best_node_side].op == lall)
                    {
                        best_node = n;
                        best_node_side = side;
                    }

                    break;
                case lall:
                    if (!best_node   ||   (best_node.f[best_node_side].op == lall && best_node.last_ts[side] > n.last_ts[side]))
                    {
                        if (n.root.used_consts[side].length == 0  ||  n.inst_consts.length < n.root.used_consts[side].length) {
                            best_node = n;
                            best_node_side = side;
                        }
                    }

                    break;
            }
        }
    }

    if (best_node) {

        let newf;

        let side = best_node_side;
        let f = best_node.f[best_node_side];
        //let new_used_consts  = [[], []];

        if (f.op == lall)
        {
            /*if (best_node.used_consts[side].length == 0)
                best_node.used_consts[side] = ['w' + String.fromCharCode(0x2080) ];
             */
            for (let c of best_node.root.used_consts[side])
            {
                if (!best_node.inst_consts.includes(c))
                {
                    newf = subst_clone(f.e, f.v, c);
                    best_node.inst_consts.push(c);
                    break;
                }
            }
            best_node.last_ts[side] = ++global_ts;
        }
        else {
            let c = make_a_const(best_node, side);
            //new_used_consts[side].push(c);
            newf = subst_clone(f.e, f.v, c);
            best_node._solved[side] = true;
            best_node.root.used_consts[side].push(c);
        }

        append_to_leaves(best_node, null, side,{f: newf, pos: true /*, new_used_consts: new_used_consts  */} );
    }


    return;
}


function tin_solve(m /* node */) /*bool*/ {

    let jobbing = true;
    while (jobbing) {
        jobbing = false;

        let q = [m]; /* queue */
        for (let i = 0; i < q.length; ++i) {
            let n = q[i]; //q.length - i - 1
            q = q.concat(n.children);

            //if (n.solved()) continue;

            let g = n.get_P_or_R();
            if (!g)
                continue;
            let [side, R, R_vars] = g;

            let other_side = 1 - side;

            let alives = n.alive_above_and_below();


            for (let alv of alives) {
                let z = alv.get_Z();
                if (!z)
                    continue;

                if (z[side] != R_vars[0])
                    continue;

                let use_code = z[other_side] + R + R_vars.join(',');

                if (n.used_bridges.includes(use_code))
                    continue;

                if (use_code == 'd₁Pc₁')
                {
                    console.log("d₁Pc₁");
                }

                n.used_bridges.push(use_code);

                let lower_node = n.depth < alv.depth ? alv : n;
                let new_consts = [];
                let temp;
                let newf = {rel: R, vs: R_vars.map(
                    x  =>  x == z[side]  ?  z[other_side] : ((temp = make_a_const(lower_node, other_side, true)), new_consts.push(temp), temp)
                )};

                n.root.used_consts[other_side] = n.root.used_consts[other_side].concat(new_consts);

                let z_part = "interrupting"; // to signal that although this node will not have a Z part,
                                             // it still is an interrupting node (comes from her sister's branch)
                if (new_consts.length)
                {
                    z_part = [ R_vars[1], new_consts[0] ];
                    if (side === 1)
                        z_part.reverse();
                }

                if (html_str_formula(newf) == 'Rd1d2')
                {
                    console.log(newf);
                }

                append_to_leaves(lower_node, null, other_side, { f: newf, pos: true }, undefined, z_part);
                jobbing = true;
                return;
            }
        }
    }

    return;
}


function solve(m /* node */, steps /* [node] */, timeout = get_time(), what_to_do = {prop: true, fol: false, tin: false}) /*bool*/
{
    if (!steps)
        steps = 1;
    if (steps > timeout)
        throw "too long";

   if (what_to_do.prop)
       prop_solve(m);
   if (what_to_do.fol)
       fol_solve(m);

   for (let i = 0; i < timeout; ++i)
   {
       prop_solve(m);
       //display(m);
       fol_solve(m);
       //display(m);
       prop_solve(m);
       //display(m);
       tin_solve(m);
       //display(m);
       console.log(i);
   }

    return;

}

var r;
function start_tin(fstr) {
    r = new node();
    r.used_consts = [['c'], ['d']];
    r.Z_pair = r.used_consts.flat();
    r.f = [frm_parse(fstr), frm_parse(fstr.replace(/c/g, 'd') )];
    r.positive = [true, false];
    solve(r);
    display(r)
}

function to_interim(n) {
    if (n.contradictory_with)
    {
        let index = (n.contr_pos + 1) / 2;
        let me = n.f[index];

        let other_n = n.contradictory_with;
        let is_boxed = n.interrupting || other_n.interrupting;

        if (is_boxed)
        {
            if (me.rel == 'P'  ||  me.rel == 'R')
            {
                return index == 0  ?  { op: lnot, e: me }  :  me;
            }
        }
        else
        {
            return  { op: index == 0   ?  lfals  :  ltrue };
            //return index == 0  ?  { op: lnot, e: n.f[index] }  :  me;
        }
    }

    let povrat;

    // disjunkcija?
    if (n.children.length == 2)
    {
        povrat = { e1: to_interim(n.children[0]), e2: to_interim(n.children[1]) };
        // s lijeve strane?
        if (n.children[0].choose_side() == 0)
        {
            povrat.op = lor;
            if (povrat.e1.op == ltrue  ||  povrat.e2.op == ltrue)
                povrat = {op: ltrue};
            else if (povrat.e1.op == lfals)
                povrat = povrat.e2;
            else if (povrat.e2.op == lfals)
                povrat = povrat.e1;
        }

        // s desne?
        else {
            povrat.op = land;
            if (povrat.e1.op == lfals  ||  povrat.e2.op == lfals)
                povrat = {op: lfals};
            else if (povrat.e1.op == ltrue)
                povrat = povrat.e2;
            else if (povrat.e2.op == ltrue)
                povrat = povrat.e1;
        }
    }
    // obična grana?
    else
    {
        if (n.children[0] == undefined)
            console.log(n);
        povrat = to_interim(n.children[0]);
    }


    // treba li prefiks povratu?
    if (n.interrupting)
    {
        let side = n.choose_side();
        let me = n.f[side];
        if (me.rel == 'R')
        {
            return { op:  side == 0  ?  lall : lexists,   e: povrat,   v: me.vs[1]  };
        }
    }

    return povrat;
}

// stapanje asocijativnih operatora
function log_flatten(f, op) {

    if (op && op == f.op)
    {
        return log_flatten(f.e1, op).concat(log_flatten(f.e2, op));
    }
    else if (f.op == lor || f.op == land)
    {
        let g = { op: f.op  };
        let es = log_flatten(f, f.op);

        /* remove dupl */
        let unique_eq = es.filter((v, i, a) => a.findIndex(  obj => ext_formulas_eql(obj, v)  ) === i);

        /* partition */
        g.es = unique_eq;

        /*
        g.e1 = unique_eq[0];
        g.e2 = unique_eq[1];
        unique_eq.splice(0, 2);
        while (unique_eq.length)
        {
            g = { op: f.op, e1: unique_eq[0], e2: g };
            unique_eq.splice(0, 1);
        }
        */

        return [g];
    }
    else
    {
        // kvantifikator [negacija ili relacija se vraćaju as-is]
        if (f.op == lall || f.op == lexists )
        {
            let g = JSON.parse(JSON.stringify(f));
            g.e = log_flatten(g.e)[0];
            return [g];
        }
    }
    return [f];
}

// cn = dn
function cmp_vars(v, mv)
{
    return mv.length == 1 && v.length == 1   ||  mv.substring(1) == v.substring(1);
}


// only for extended formulas
function has_var(f, v) {
    if (f.op == lor || f.op == land)
    {
        for (let e of f.es)
            if (has_var(e, v))
                return true;
    }
    else if (f.op == lnot)
        return has_var(f.e, v)
    else if (f.op == lall || f.op == lexists)
        return has_var(f.e, v);
    else // rel
    {
        for (let mv of f.vs)
            if (cmp_vars(v, mv))
                return true;
        return false;
    }
}

/*
    Ax(Rcx -> Ay(Rxy -> Py)) -> Pc
    f = log_flatten(frm_parse('Ex(Rcx & Ey(Rxy & ~ Py)) |  Pc'))[0]
    f = f)[0]

 */

// Ax(P & Qx) -> P & Ax(Qx)
function aggresive_fix_quantifiers(f, q, mother_obj, child_name) {

    if (f.solved) // kvantifikator
    {
        fix_quantifiers(f.e, q, f, 'e');

        return;
    }

    if (q)
    {
        if (f.op == lor || f.op == land)
        {
            let imaju_q  = f.es.filter( g =>  has_var(g, q.v) );
            let nemaju_q = f.es.filter( g => !has_var(g, q.v) );

            // ništa nije kvantificirano varijablom q?
            if (imaju_q.length == 0)
            {
                // kvantifikator premješten u praznost

                for (let [ind, e] of f.es.entries())
                    fix_quantifiers(e, undefined, f.es, ind);

                return;
            }
            // sve je kvantificirano varijablom q? onda smo našli pravo mjesto
            else if (imaju_q.length == f.es.length)
            {
                if (imaju_q.length > 1)
                {
                    mother_obj[child_name] = q;
                    q.e = f;

                    for (let [ind, e] of f.es.entries())
                        fix_quantifiers(e, undefined, f.es, ind);
                    return;
                }
                else
                {
                    // točno jedan operand postoji i ima varijable: treba ga inspektat
                    fix_quantifiers(imaju_q[0], q, f.es, 0);

                    return;
                }
            }
            // inače, nešto ima q, a nešto nema
            else
            {
                if (imaju_q.length > 1)
                {
                    q.e = { op: f.op,  es: imaju_q };
                    q.solved = true;
                    f.es = [ q, ...nemaju_q ];

                    for (let [ind, e] of f.es.entries())
                        fix_quantifiers(e, undefined, f.es, ind);

                    return;
                }
                else
                {
                    fix_quantifiers(imaju_q[0], q, f.es, f.es.indexOf(imaju_q[0]));

                    return;
                }

            }
        }
        else if (f.op == lall || f.op == lexists)
        {
            fix_quantifiers(f.e, q, f, 'e');

            let q2 = { v: f.v,  op: f.op };

            // brisanje sebe
            mother_obj[child_name] = f.e;

            fix_quantifiers(f.e, q2, mother_obj, child_name);

            return;
        }
        // rel ili neg
        else
        {
            mother_obj[child_name] = q;
            q.e = f;

            return;
        }


    } // if (q)


    if (f.es)
        for (let [ind, e] of f.es.entries())
            fix_quantifiers(e, undefined, f.es, ind);
    else if (f.e1)
        fix_quantifiers(f.e1, undefined, f, 'e1');
    else if (f.e && (f.op == lall || f.op == lexists) )
    {
        let q = { v: f.v,  op: f.op };

        // brisanje sebe
        mother_obj[child_name] = f.e;

        fix_quantifiers(f.e, q , mother_obj, child_name);

        return;
    }
    else if (f.e)
        fix_quantifiers(f.e, undefined, f, 'e');

    return;
}


function fix_quantifiers(f, q, mother_obj, child_name) {

    if (f.solved) // kvantifikator
    {
        fix_quantifiers(f.e, q, f, 'e');

        return;
    }

    if (q)
    {
        if (f.op == lor || f.op == land)
        {
            let imaju_q  = f.es.filter( g =>  has_var(g, q.v) );
            let nemaju_q = f.es.filter( g => !has_var(g, q.v) );

            // ništa nije kvantificirano varijablom q?
            if (imaju_q.length == 0)
            {
                // kvantifikator premješten u praznost

                for (let [ind, e] of f.es.entries())
                    fix_quantifiers(e, undefined, f.es, ind);

                return;
            }
            // sve je kvantificirano varijablom q? onda smo našli pravo mjesto
            else if (imaju_q.length == f.es.length)
            {
                if (imaju_q.length > 1)
                {
                    mother_obj[child_name] = q;
                    q.e = f;

                    for (let [ind, e] of f.es.entries())
                        fix_quantifiers(e, undefined, f.es, ind);
                    return;
                }
                else
                {
                    // točno jedan operand postoji i ima varijable: treba ga inspektat
                    fix_quantifiers(imaju_q[0], q, f.es, 0);

                    return;
                }
            }
            // inače, nešto ima q, a nešto nema
            else
            {
                if (imaju_q.length > 1)
                {
                    q.e = { op: f.op,  es: imaju_q };
                    q.solved = true;
                    f.es = [ q, ...nemaju_q ];

                    for (let [ind, e] of f.es.entries())
                        fix_quantifiers(e, undefined, f.es, ind);

                    return;
                }
                else
                {
                    fix_quantifiers(imaju_q[0], q, f.es, f.es.indexOf(imaju_q[0]));

                    return;
                }

            }
        }
        else if (f.op == lall || f.op == lexists)
        {
            //fix_quantifiers(f.e, q, f, 'e');
            mother_obj[child_name] = q;
            q.e = f.e;

            let q2 = { v: f.v,  op: f.op };

            // brisanje sebe
            // mother_obj[child_name] = f.e;

            fix_quantifiers(f.e, q2, q, 'e');

            return;
        }
        // rel ili neg
        else
        {
            mother_obj[child_name] = q;
            q.e = f;

            return;
        }


    } // if (q)


    if (f.es)
        for (let [ind, e] of f.es.entries())
            fix_quantifiers(e, undefined, f.es, ind);
    else if (f.e1)
        fix_quantifiers(f.e1, undefined, f, 'e1');
    else if (f.e && (f.op == lall || f.op == lexists) )
    {
        let q = { v: f.v,  op: f.op };

        // brisanje sebe
        mother_obj[child_name] = f.e;

        fix_quantifiers(f.e, q , mother_obj, child_name);

        return;
    }
    else if (f.e)
        fix_quantifiers(f.e, undefined, f, 'e');

    return;
}

function simplify(f) {
    let g = log_flatten(f)[0];
    let meta = { e: g }
    fix_quantifiers(g, undefined, meta, 'e');
    return meta.e;
}

function to_modal(f, v = 'c') {
    if (f.op == lfals || f.op == ltrue)
        return f;
    if (f.op == lall || f.op == lexists) {
        /* expect lor or land */
        if (((f.op == lexists && f.e.op == lor) || (f.op == lall && f.e.op == land)) && f.e.es.length > 1)
            throw "problem: " + html_str_formula(f) + " uz vanjsku varijablu " + v + " [kvantifikator i veznik se ne slazu]";

        let preostala;
        let djeca = (f.e.op == lor || f.e.op == land) ? f.e.es  :  [ f.e ];

        let i = null;
        for (let [ind, Rcx] of djeca.entries()) {
            if (f.op == lall && Rcx.op == lnot && Rcx.e.rel == 'R' && cmp_vars(Rcx.e.vs[0], v) && cmp_vars(Rcx.e.vs[1], f.v)) {
                i = ind;
                break;
            }
            if (f.op == lexists && Rcx.rel == 'R' && cmp_vars(Rcx.vs[0], v) && cmp_vars(Rcx.vs[1], f.v)) {
                i = ind;
                break;
            }
        }
        if (i === null)
            throw "problem: " + html_str_formula(f) + " uz vanjsku varijablu " + v + " [nema očekivanog R-literala pod kvantifikatorom]";

        preostala = djeca.filter((dijete, ind) => ind != i).map(g => to_modal(g, f.v));



        return {
            op: f.op,
            e: preostala.length == 0 ? {op: f.op == lall ? lfals : ltrue} : preostala.length == 1 ? preostala[0] : {
                op: f.e.op,
                es: preostala
            }
        };
    }
    if (f.op == lor || f.op == land) {
        return {op: f.op, es: f.es.map(g => to_modal(g, v)) };
    }
    if (f.op == lnot) {
        return {op: f.op, e: to_modal(f.e, v)};
    }
    if (!f.rel || f.rel == 'R' || !cmp_vars(f.vs[0], v))
        throw "problem: " + html_str_formula(f) + " uz vanjsku varijablu " + v + " [očekujem literal koji nije R-literal i ima vanjsku varijablu, umjesto ove formule]";

    return { rel: f.rel, vs: [] }

}


    // to_modal({ op: lall, vs: ['x'], e: { op: lcond, e1: { rel: 'R', vs: ['x', 'y'] }, e2: { rel: 'P', vs: ['y'] }  }  })


