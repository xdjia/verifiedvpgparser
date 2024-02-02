import re, glob, os

html_tokens = glob.glob("Data/html/*.tokens")

for file in html_tokens:
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
