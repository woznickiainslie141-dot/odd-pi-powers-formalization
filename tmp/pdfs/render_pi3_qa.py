from pathlib import Path
import json
import pypdfium2 as pdfium
from PIL import Image, ImageOps, ImageDraw

root = Path(__file__).resolve().parents[2]
pdf_path = root/'output/pdf/pi3_explicit_bound/main.pdf'
out = root/'tmp/pdfs/pi3_qa'
out.mkdir(exist_ok=True)
pdf = pdfium.PdfDocument(pdf_path)
alltext = []
thumbs = []
for i, page in enumerate(pdf):
    img = page.render(scale=1.6).to_pil().convert('RGB')
    img.save(out/f'page-{i+1:02d}.png')
    tx = page.get_textpage().get_text_range()
    alltext.append(tx)
    thumb = ImageOps.contain(img, (320,460))
    tile = Image.new('RGB',(340,490),'#ededed')
    tile.paste(thumb,((340-thumb.width)//2,10))
    ImageDraw.Draw(tile).text((12,470),f'Page {i+1}',fill='black')
    thumbs.append(tile)
sheet = Image.new('RGB',(340*3,490*3),'white')
for i,tile in enumerate(thumbs):
    sheet.paste(tile,((i%3)*340,(i//3)*490))
sheet.save(out/'contact-sheet.png')
(out/'extracted.txt').write_text('\n\f\n'.join(alltext),encoding='utf-8')
print(json.dumps({'pages':len(pdf),'first_page_text':alltext[0][:550]},
                 ensure_ascii=True))
