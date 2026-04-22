import os

def process_lean_files(directory):
    for root, dirs, files in os.walk(directory):
        # 排除所有以 . 开头的隐藏文件夹（如 .lake）
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        
        for file in files:
            if file.endswith(".lean"):
                filepath = os.path.join(root, file)
                with open(filepath, 'r', encoding='utf-8') as f:
                    content = f.read()

                if "module" in content.split("-/")[1][:20] if "-/" in content else False:
                    continue

                if "-/" in content:
                    parts = content.split("-/", 1)
                    header = parts[0] + "-/\nmodule\n\n"
                    body = parts[1].lstrip()
                    
                    lines = body.split('\n')
                    new_lines = []
                    imports_done = False
                    for i, line in enumerate(lines):
                        if line.startswith("import "):
                            new_lines.append("public " + line)
                        elif line.strip() == "" and not imports_done and new_lines and new_lines[-1].startswith("public import"):
                            pass
                        elif not line.startswith("import ") and not imports_done:
                            if new_lines and new_lines[-1].startswith("public import"):
                                new_lines.append("\npublic section")
                                new_lines.append("\n" + line)
                            else:
                                new_lines.append(line)
                            imports_done = True
                        else:
                            new_lines.append(line)

                    if not imports_done and any(l.startswith("public import") for l in new_lines):
                         new_lines.append("\npublic section")

                    new_content = header + '\n'.join(new_lines).strip() + '\n'

                    with open(filepath, 'w', encoding='utf-8') as f:
                        f.write(new_content)

if __name__ == "__main__":
    # 明确指定只处理 QuillenSuslin 文件夹
    process_lean_files("QuillenSuslin")