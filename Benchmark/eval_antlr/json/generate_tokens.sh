ANTLR="../antlr-4.11.1-complete.jar"

gname="json"
output_dir="Tokens"

rm -rf $output_dir && mkdir $output_dir

for f in $(ls ../../bench_files/${gname}_files/*.${gname}); do
    # NOTE - Remove the suffix
    name=${f%.${gname}}
    # NOTE - Remove the path
    name=${name##*/}
    echo $name
    java -cp $ANTLR:./antlr_build org.antlr.v4.gui.TestRig JSON json $f -tokens > $output_dir/$name.tokens || (exit(1))
done

token_dir="../../Data/json/"
rm -rf $token_dir && mkdir $token_dir && mv Tokens/* $token_dir