# NOTE - Evaluate the perfomance of ANTLR in parsing HTML files

ANTLR="../antlr-4.11.1-complete.jar"

output_file=results/eval_antlr.html.result

rm -rf results/ && mkdir results && touch $output_file

for f in $(ls ../../bench_files/html_files/*.html); do
    # NOTE - Remove the suffix
    name=${f%.html}
    # NOTE - Remove the path
    name=${name##*/}
    echo $name
    echo $name >>$output_file
    java -cp $ANTLR:./antlr_build TestHTML $f >>$output_file || (exit(1))
done
