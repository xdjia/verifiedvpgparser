# NOTE - Evaluate the perfomance of bison in parsing JSON files

output_file=results/eval_bison.json.result

rm -rf results/ && mkdir results && touch $output_file

for f in $(ls ../../bench_files/json_files/*.json); do
    # NOTE - Remove the suffix
    name=${f%.json}
    # NOTE - Remove the path
    name=${name##*/}
    echo $name >>$output_file
    echo $name 
    java -cp build JSON main $f >>$output_file
done
