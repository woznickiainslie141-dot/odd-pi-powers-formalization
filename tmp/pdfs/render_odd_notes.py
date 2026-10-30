from pathlib import Path
import json
import pypdfium2 as pdfium
from PIL import Image,ImageOps,ImageDraw

root=Path(__file__).resolve().parents[2]
pdf=pdfium.PdfDocument(root/"output/pdf/odd_pi_powers_notes/main.pdf")
dest=root/"tmp/pdfs/odd_pi_notes_qa"
dest.mkdir(exist_ok=True)
tiles=[]
text=[]
for i,page in enumerate(pdf):
    im=page.render(scale=1.7).to_pil().convert("RGB")
    im.save(dest/f"page-{i+1:02d}.png")
    text.append(page.get_textpage().get_text_range())
    thumb=ImageOps.contain(im,(290,410))
    tile=Image.new("RGB",(310,440),"#eceff1")
    tile.paste(thumb,((310-thumb.width)//2,8))
    ImageDraw.Draw(tile).text((12,423),f"PDF page {i+1}",fill="black")
    tiles.append(tile)
for start in range(0,len(tiles),8):
    sheet=Image.new("RGB",(1240,880),"white")
    for j,tile in enumerate(tiles[start:start+8]):
        sheet.paste(tile,((j%4)*310,(j//4)*440))
    sheet.save(dest/f"contact-{start//8+1}.png")
(dest/"extracted.txt").write_text("\n\f\n".join(text),encoding="utf-8")
report={
    "pages":len(pdf),
    "text_characters":sum(map(len,text)),
    "contains_expected_bounds":all(s in "".join(text)
        for s in ("1203.973","42461","1272103","35398937")),
    "per_page_characters":[len(t) for t in text],
}
(dest/"qa_report.json").write_text(json.dumps(report,indent=2),encoding="utf-8")
print(json.dumps(report,indent=2))
