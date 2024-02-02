# NOTE - Evaluate the perfomance of ANTLR in parsing XML files

ANTLR="../antlr-4.11.1-complete.jar"

output_file=results/eval_antlr.xml.result

rm -rf results/ && mkdir results && touch $output_file

for f in $(ls ../../bench_files/xml_files/*.xml); do
    # NOTE - Remove the suffix
    name=${f%.xml}
    # NOTE - Remove the path
    name=${name##*/}
    echo $name >>$output_file
    echo $name
    java -cp $ANTLR:./antlr_build TestXML $f >>$output_file || (exit(1))
done
