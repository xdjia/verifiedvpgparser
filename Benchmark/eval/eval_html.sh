# NOTE - Evaluate the perfomance of vpg parser in lexing HTML files

dune build --release parse/parse_html.exe

output_file=results/vpg.eval_html.csv

rm -rf $output_file && touch $output_file

# NOTE - print csv header
echo "name,parse,extract,tree" >>$output_file

for f in $(ls Data/html/*.data); do
    # NOTE - Remove the suffix
    name=${f%.data}
    # NOTE - Remove the path
    name=${name##*/}
    echo $name
    echo -n $name, >> $output_file
    _build/default/parse/parse_html.exe $f >>$output_file
done