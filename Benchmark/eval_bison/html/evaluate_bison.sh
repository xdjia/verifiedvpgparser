# NOTE - Evaluate the perfomance of bison in parsing HTML files

output_file=results/eval_bison.html.result

rm -rf results/ && mkdir results && touch $output_file

for f in $(ls ../../bench_files/html_files/*.html); do
    # NOTE - Remove the suffix
    name=${f%.html}
    # NOTE - Remove the path
    name=${name##*/}
    echo $name >>$output_file
    echo $name 
    java -cp build HTML main $f >> $output_file
done
