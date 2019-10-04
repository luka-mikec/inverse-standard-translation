var status_div = document.querySelector("#status"),
    in_div = document.querySelector("#in"),
    out_div = document.querySelector("#out"),
    out_sequent = document.querySelector("#out_sequent"),
    out_lat_div = document.querySelector("#out_lat"),
    out_dbg_div = document.querySelector("#out_dbg");



function display(n) {
    while (out_sequent.firstChild)
        out_sequent.firstChild.remove()
    out_sequent.appendChild(n.html_print());
}

function compile() {
    //try
    {
        /*let f = frm_parse(in_div.value.trim());

        window.f = f;

        let n = new node();
        n.f = f;

        solve(n);

        display(n);*/

        out_lat_div .innerHTML = "Error."

        start_tin(in_div.value.trim());
        let str1 = "Bisimulation invariant: " + ((r.open_leaves().length == 0) ? "yes." : "no, or need more steps to determine. (Current size: " + r.tree_nodes().length + " nodes)") + "\n";
        out_lat_div .innerHTML = str1

        interim = to_interim(r);

        let str2 = "Interim formula: " + html_str_formula(interim).replace(/[cd]/g, 'x') + "\n"
        out_lat_div.innerHTML += str2;

        simpl = simplify(interim);

        let str3 = "Simplified interim formula: " + html_str_formula(simpl).replace(/[cd]/g, 'x') + "\n";
        out_lat_div.innerHTML += str3

        modal = to_modal(simpl);
        modal_rep = html_str_formula(modal).replace(new RegExp(html[lall], 'g'), '◻').replace(new RegExp(html[lexists], 'g'), '◇');

        let str4 = "Modal formula: " + modal_rep + "\n";
        out_lat_div.innerHTML += str4;

        out_lat_div.innerHTML = str1 + "\n" + str4 + "\n" + str3 + "\n" + str2;



        out_div.children[0].scrollLeft = 19100

        // out_lat_div.innerHTML = s.latex_print();
    }
    //catch (e) { throw e; }

}

