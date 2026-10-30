from pathlib import Path
import shutil
import json
import zipfile
import hashlib
import sys

ROOT=Path(__file__).resolve().parents[1]
PROJECT=ROOT/"output/pdf/odd_pi_powers_notes"

def prepare():
    for src,dest,old,new in [
        ("test_scalar_arcsin_pade.py","experiment_arcsin.py",
         'Path(__file__).with_name("scalar_arcsin_pade_2026-10-27.json")',
         '(Path(__file__).resolve().parents[1]/"data"/"experiment_arcsin.json")'),
        ("test_derivative_beta3.py","experiment_beta3.py",
         'Path(__file__).with_name("derivative_beta3_screen_2026-10-27.json")',
         '(Path(__file__).resolve().parents[1]/"data"/"experiment_beta3.json")'),
    ]:
        text=(ROOT/"research"/src).read_text(encoding="utf-8")
        assert old in text
        (PROJECT/"code"/dest).write_text(text.replace(old,new),encoding="utf-8")
    print("Optional experiment programs prepared.")

def package():
    pdf=ROOT/"output/pdf/odd_pi_powers_notes.pdf"
    shutil.copy2(PROJECT/"main.pdf",pdf)
    paths=[PROJECT/"main.tex",PROJECT/"main.pdf",PROJECT/"README.md",
           PROJECT/"requirements.txt"]
    for directory,pattern in [("sections","*.tex"),("code","*.py"),
                              ("data","*.json"),("data","*.tex")]:
        paths.extend(sorted((PROJECT/directory).glob(pattern)))
    manifest={str(p.relative_to(PROJECT)).replace("\\","/"):
              hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    (PROJECT/"data/source_manifest.json").write_text(
        json.dumps(manifest,indent=2)+"\n",encoding="utf-8")
    paths.append(PROJECT/"data/source_manifest.json")
    archive=ROOT/"output/pdf/odd_pi_powers_notes_source.zip"
    with zipfile.ZipFile(archive,"w",zipfile.ZIP_DEFLATED) as z:
        for p in paths:
            z.write(p,"odd_pi_powers_notes/"+p.relative_to(PROJECT).as_posix())
    with zipfile.ZipFile(archive) as z:
        assert z.testzip() is None
        assert z.read("odd_pi_powers_notes/main.pdf")==pdf.read_bytes()
    print(json.dumps({"pdf":str(pdf),"archive":str(archive),
          "source_files":len(paths),"pdf_sha256":manifest["main.pdf"]},indent=2))

if __name__=="__main__":
    if len(sys.argv)>1 and sys.argv[1]=="package":
        package()
    else:
        prepare()
