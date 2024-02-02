# NOTE - Evaluate the perfomance of bison in parsing XML files

output_file=results/eval_bison.xml.result

rm -rf results/ && mkdir results && touch $output_file

for f in $(ls ../../bench_files/xml_files/*.xml); do
    # NOTE - Remove the suffix
    name=${f%.xml}
    # NOTE - Remove the path
    name=${name##*/}
    echo $name >>$output_file
    echo $name
    java -cp build XML main $f >>$output_file
done