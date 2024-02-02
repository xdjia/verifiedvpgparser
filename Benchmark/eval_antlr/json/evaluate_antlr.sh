# NOTE - Evaluate the perfomance of ANTLR in parsing JSON files

ANTLR="../antlr-4.11.1-complete.jar"

output_file=results/eval_antlr.json.result

rm -rf results/ && mkdir results && touch $output_file

for f in $(ls ../../bench_files/json_files/*.json); do
    # NOTE - Remove the suffix
    name=${f%.json}
    # NOTE - Remove the path
    name=${name##*/}
    echo $name >>$output_file
    echo $name
    java -cp $ANTLR:./antlr_build TestJSON $f >>$output_file
done

token_dir="../../Data/json/"
rm -rf $token_dir && mkdir $token_dir && mv Tokens $token_dir