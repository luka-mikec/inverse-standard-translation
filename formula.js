/*

    This file contains generic functions related to formula processing (parsing, substitution, printing etc.)

    There are also unrelated bits, such as translations, which have to do with global state.

    Languages are global dicts, current language is saved in the "clang", and refresh_dict should be called to apply changes.

 */


var land = '/\\', lor = '\\/', lcond = '->', liff = '<->', lnot = '~', lfals = '#', lreit='re',
    lintro = 'i', lelim = 'e', lall = 'A', lexists = 'E', lasm = 'assump.', ltrue = 'T';

var synonyms = {
    "#": ["#", "_|_"],
    "T": ["T"],
    "/\\": ["/\\", "&" , "&&" , "*" , "."],
    "\\/": ["\\/",  "|" , "||" , "+" , ","],
    "->": ["->", "=>", ">"],
    "<->": ["<->", "<=>" , "=" , "<>"],
    "~": ["¬" , "~" , "-"],
    "A": ["A", "@"],
    "E": ["E"],

};

function synonym_base(symb) {
    for (let k of Object.keys(synonyms))
    {
        if (synonyms[k].includes(symb) )
            return k ;
    }
    throw "uknown symbol " + symb;
}

var latex = {};
latex[lasm] =  '\\text{assump.}';
latex[land] = '\\wedge ';
latex[lor] = '\\vee ';
latex[lcond] = '\\to ';
latex[liff] = '\\leftrightarrow ';
latex[lall] = '\\forall ';
latex[lexists] = '\\exists ';
latex[lnot] = '\\neg ';
latex[lfals] = '\\bot ';
latex[ltrue] = '\\top ';
latex[lreit] = '\\text{re.}';

var html = {};
html[land] = '∧';
html[lor] = '∨';
html[lcond] = '→';
html[liff] = '↔';
html[lall] = '∀';
html[lexists] = '∃';
html[lnot] = '¬';
html[lfals] = '⊥';
html[ltrue] = '⊤';
html[lreit] = 're.';
html[lasm] = 'assump.';

function subst_inst_of(inst, schema, transl, abusive /* if t/x and have subformula QxP(t), reject */)
{
    if (inst.op !== schema.op)
        return false;

    if (inst.rel)
    {
        if (inst.rel != schema.rel || inst.vs.length != schema.vs.length)
            return false;
        for (let [i, obj] of inst.vs.entries())
        {
            if (transl.ignore_transl)
            {
                if (obj != schema.vs[i])
                    return false;
            }
            else
            {
                if (schema.vs[i] == transl.v)
                {
                    if (transl.c == null)
                    {
                        transl.c = obj;
                    }
                    else if (transl.c != obj && (transl.total  ||  obj != schema.vs[i]))
                    {
                        return false;
                    }
                }
                else if (schema.vs[i] != obj)
                    return false;
            }
        }
        return true;
    }

    switch (inst.op) {
        case lfals: case ltrue:
            return true;
        case lnot:
            return subst_inst_of(inst.e, schema.e, transl, abusive);
        case land: case lor: case lcond: case liff:
            return subst_inst_of(inst.e1, schema.e1, transl, abusive) && subst_inst_of(inst.e2, schema.e2, transl, abusive);
        case lall: case lexists:
            if (inst.v !== schema.v)
                return false;

            if (transl.ignore_transl || inst.v === transl.v) {
                let old_ignore_transl = transl.ignore_transl;
                transl.ignore_transl = true;
                let istrue = subst_inst_of(inst.e, schema.e, transl, abusive);

                if (abusive && has_constant(schema.e, transl.c))
                    return false;

                transl.ignore_transl = old_ignore_transl;
                return istrue;
            }

            return subst_inst_of(inst.e, schema.e, transl, abusive);
    }
}

function formulas_eql(f, g)
{
    return subst_inst_of(f, g, { ignore_transl: true }, false);
}

/* extended version uses "es" instead of e, e1 and e2, for arbitrary-length conjs/disjs */

function ext_subst_inst_of(inst, schema, transl, abusive /* if t/x and have subformula QxP(t), reject */)
{
    if (inst.op !== schema.op)
        return false;

    if (inst.rel)
    {
        if (inst.rel != schema.rel || inst.vs.length != schema.vs.length)
            return false;
        for (let [i, obj] of inst.vs.entries())
        {
            if (transl.ignore_transl)
            {
                if (obj != schema.vs[i])
                    return false;
            }
            else
            {
                if (schema.vs[i] == transl.v)
                {
                    if (transl.c == null)
                    {
                        transl.c = obj;
                    }
                    else if (transl.c != obj && (transl.total  ||  obj != schema.vs[i]))
                    {
                        return false;
                    }
                }
                else if (schema.vs[i] != obj)
                    return false;
            }
        }
        return true;
    }

    switch (inst.op) {
        case lfals: case ltrue:
            return true;
        case lnot:
            return ext_subst_inst_of(inst.e, schema.e, transl, abusive);
        case land: case lor: case lcond: case liff:
            if (inst.es) {
                if (inst.es.length != schema.es.length)
                    return false;
                for (let i = 0; i < inst.es.length; ++i) {

                    if (!ext_subst_inst_of(inst.es[i], schema.es[i], transl, abusive))
                        return false;
                }
                return true;
            }
            else
            {
                return ext_subst_inst_of(inst.e1, schema.e1, transl, abusive) && ext_subst_inst_of(inst.e2, schema.e2, transl, abusive);
            }
        case lall: case lexists:
            if (inst.v !== schema.v)
                return false;

            if (transl.ignore_transl || inst.v === transl.v) {
                let old_ignore_transl = transl.ignore_transl;
                transl.ignore_transl = true;
                let istrue = ext_subst_inst_of(inst.e, schema.e, transl, abusive);

                if (abusive && has_constant(schema.e, transl.c))
                    return false;

                transl.ignore_transl = old_ignore_transl;
                return istrue;
            }

            return ext_subst_inst_of(inst.e, schema.e, transl, abusive);
    }
}

function ext_formulas_eql(f, g) {
    return ext_subst_inst_of(f, g, { ignore_transl: true }, false);
}

function formulas_contradictory(f, g)
{
    return f.op == lnot && formulas_eql(f.e, g)  ||  g.op == lnot && formulas_eql(g.e, f);
}

function inconsistent_set(s)
{
    for (let a of s)
        for (let b of s)
            if (formulas_contradictory(a, b))
                return true;

    return false;
}

function deep_copy(frm, to) {
    if (!to)
        return JSON.parse(JSON.stringify(frm));
    else
        Object.assign(to, JSON.parse(JSON.stringify(frm)));
}

function has_constant(form, c, not_consts)
{
    if (!not_consts)
        not_consts = [];

    if (form.rel)
    {
        return form.vs.includes(c);
    }

    switch (form.op) {
        case lfals: case ltrue:
            return false;
        case lall: lexists:
            not_consts = not_consts.slice();
            not_consts.push(form.v);
            return has_constant(form.e, c, not_consts);
        case lnot:
            return has_constant(form.e, c, not_consts);
        case land: case lor: case lcond: case liff:
            return has_constant(form.e1, c, not_consts) || has_constant(form.e2, c, not_consts);
    }
}

function subst(form, v, c)
{
    if (form.rel)
    {
        form.vs = form.vs.map(x => x == v ? c : x);
    }

    switch (form.op) {
        case lfals: case ltrue:
            return;
        case lall: case lexists: case lnot:
            subst(form.e, v, c);
            return;
        case land: case lor: case lcond: case liff:
            subst(form.e1, v, c);
            subst(form.e2, v, c);
            return;
    }
}

function subst_clone(form, v, c)
{
    let f = deep_copy(form);
    subst(f, v, c);
    return f;
}



function frm_terms(form, bound)
{
    if (!bound)
        bound = [];

    if (form.rel)
    {
        return form.vs.filter(x => ! bound.includes(x));
    }

    switch (form.op) {
        case lfals: case ltrue:
            return [];
        case lall: case lexists:
            return frm_terms(form.e, bound.concat(form.v));
        case lnot:
            return frm_terms(form.e, bound);
        case land: case lor: case lcond: case liff:
            return frm_terms(form.e1, bound).concat(frm_terms(form.e2, bound));
    }
}

var hr = {
    'asm': 'pretp.',
    'e': 'i',
    'i': 'u',
    'reit': 'op.',
}, en = {
    'asm': 'assump.',
    'e': 'e',
    'i': 'i',
    'reit': 're.',
};

var clang = en;

function refresh_lang() {
    //lintro = window.clang['intro'];
    //lelim = window.clang['elim'];
    //lasm = window.clang['asm'];

    latex[lreit] = '\\text{' + window.clang['reit'] + '}';
    html[lreit] = window.clang['reit'];

    latex[lasm] = '\\text{' + window.clang['asm'] + '}';
    html[lasm] = window.clang['asm'];
}

function html_str_formula(form, depth) {
    let str_formula = html_str_formula;
    if (!depth) depth = 0;
    if (form.rel) {
        return form.rel + form.vs.map(c => draw_a_const(c, 0)).join("");
    }
    if (form.v)
        return html[form.op] + draw_a_const(form.v) + " " + str_formula(form.e, depth + 1);
    if (form.e)
        return html[form.op] + str_formula(form.e, depth + 1);
    if (form.e1)
        return (depth > 0 ? '(' : '') + str_formula(form.e1, depth + 1) + ' ' + html[form.op] + ' ' + str_formula(form.e2, depth + 1) + (depth > 0 ? ')' : '');
    if (form.es)
        return (depth > 0 ? '(' : '') + form.es.map( g => str_formula(g, depth + 1) ).join(' ' + html[form.op] + ' ') + (depth > 0 ? ')' : '');
    if (form.op === lfals || form.op === ltrue)
        return html[form.op];

    return form;
}

function latex_str_formula(form, depth) {
    let str_formula = latex_str_formula;
    if (!depth) depth = 0;
    if (form.rel) {
        return form.rel + form.vs.join("");
    }
    if (form.v)
        return latex[form.op] + form.v + " " + str_formula(form.e, depth + 1);
    if (form.e)
        return latex[form.op] + str_formula(form.e, depth + 1);
    if (form.e1)
        return (depth > 0 ? '(' : '') + str_formula(form.e1, depth + 1) + ' ' + latex[form.op] + ' ' + str_formula(form.e2, depth + 1) + (depth > 0 ? ')' : '');
    if (form.op === lfals || form.op === ltrue)
        return latex[form.op];
    return form;
}
