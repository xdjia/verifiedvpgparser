import re, glob, os

xml_tokens = glob.glob("Data/xml/*.tokens")

for file in xml_tokens:
    with open(file, "r") as f:
        lines = f.readlines()

    data = []
    for line in lines:
        line = line.strip()
        text = re.sub(r".*[0-9]='(.*)',<(.*)>.*", r"\1", line)
        token = re.sub(r".*[0-9]='(.*)',<(.*)>.*", r"\2", line)
        data += [text, token]

    data_path = os.path.splitext(file)[0]+'.data'
    print(data_path)
    with open(data_path, "w") as f:
        f.write('\n'.join(data[:-2]))
