typeset -F SECONDS
dune build --release parse/parse_xml.exe

output_file=results/vpg.eval_xml.csv

rm -rf $output_file && touch $output_file

# NOTE - print csv header
echo "name,parse,extract,tree" >>$output_file

for f in $(ls Data/xml/*.data); do
    # NOTE - Remove the suffix
    name=${f%.data}
    # NOTE - Remove the path
    name=${name##*/}
    echo $name
    echo -n $name, >> $output_file
    _build/default/parse/parse_xml.exe $f >>$output_file
done
