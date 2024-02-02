output_file=json.token_num

rm -rf $output_file && touch $output_file

# NOTE - print csv header
echo "name,file_size,token_num" >>$output_file

for f in $(ls Data/json/*.tokens); do
    # NOTE - Remove the suffix
    name=${f%.tokens}
    # NOTE - Remove the path
    name=${name##*/}
    echo $name
    echo -n $name, >>$output_file
    stat --printf="%s" Data/json_files/$name.json >>$output_file
    echo -n , >>$output_file
    wc -l < $f >>$output_file
done

# !SECTION
