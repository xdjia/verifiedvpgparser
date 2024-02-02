ANTLR="../antlr-4.11.1-complete.jar"

output_dir="Tokens"

rm -rf $output_dir && mkdir $output_dir

for f in $(ls  ../../bench_files/html_files/*.html); do
    # NOTE - Remove the suffix
    name=${f%.html}
    # NOTE - Remove the path
    name=${name##*/}
    echo $name
    java -cp $ANTLR:./antlr_build org.antlr.v4.gui.TestRig HTML htmlDocument $f -tokens > $output_dir/$name.tokens || (exit(1))
done

token_dir="../../Data/html/"
rm -rf $token_dir && mkdir $token_dir && mv Tokens/* $token_dir