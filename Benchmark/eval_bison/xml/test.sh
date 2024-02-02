typeset -F SECONDS

start_time=$SECONDS
java -cp ./build XML main ~/Sync/XML-parse-benchmark/out/js.XML
end_time=$SECONDS
(( time = end_time - start_time ))
echo $time