dune build --release parse/parse_json.exe

output_file=results/vpg.eval_json.csv

rm -rf $output_file && touch $output_file

# NOTE - print csv header
echo "name,parse,extract,tree" >>$output_file

for f in $(ls Data/json/*.data); do
    # NOTE - Remove the suffix
    name=${f%.data}
    # NOTE - Remove the path
    name=${name##*/}
    echo -n $name, >>$output_file
    echo $name
    _build/default/parse/parse_json.exe $f >>$output_file
done
