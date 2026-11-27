"""Check every typeset page and optionally render individual pages and contact sheets for visual review."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

import fitz
from PIL import Image, ImageDraw

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument("--sheets", type=Path)
parser.add_argument("--pages", type=Path, help="Directory for reading-size PNGs rendered by Poppler")
parser.add_argument("--report", type=Path, required=True)
args = parser.parse_args()
result = {}
for name in ("Universal_Pure_S", "Symbolic_Complete_Proof"):
    path = root / "paper" / (name + ".pdf")
    log = (root / "paper" / (name + ".log")).read_text(errors="replace")
    warnings = [line for line in log.splitlines()
                if any(s in line for s in ["Overfull", "Underfull", "Missing character:", "undefined references", "undefined on input"])]
    assert not warnings, warnings
    pages = []
    renders = []
    equation_tags = []
    if args.pages:
        args.pages.mkdir(parents=True, exist_ok=True)
        prefix, dpi = ("main", 125) if name == "Universal_Pure_S" else ("sym", 135)
        subprocess.run(["pdftoppm", "-r", str(dpi), "-png", str(path), str(args.pages / prefix)], check=True)
    with fitz.open(path) as pdf:
        assert pdf.metadata["author"] == "Radames Mercado-Barbosa and Anthony Langdon"
        encoding_page = pdf[1] if name == "Universal_Pure_S" else pdf[0]
        assert "enc(nil)=S" in "".join(encoding_page.get_text().split())
        if name == "Symbolic_Complete_Proof":
            first_number = max(pdf[0].search_for("(1)"), key=lambda rect: rect.x1)
        for idx, page in enumerate(pdf):
            text = page.get_text()
            assert text.strip() and "\ufffd" not in text and "??" not in text
            missing = [chr(codepoint) for span in page.get_texttrace()
                       for codepoint, glyph, _, _ in span["chars"] if glyph == 0 and not chr(codepoint).isspace()]
            assert not missing, (name, idx + 1, missing)
            words = page.get_text("words")
            if name == "Symbolic_Complete_Proof":
                equation_tags.extend(int(w[4][1:-1]) for w in words
                                     if abs(w[2] - first_number.x1) < 1 and re.fullmatch(r"\(\d+\)", w[4]))
            lo = min(w[0] for w in words)
            hi = max(w[2] for w in words)
            assert lo > 15 and hi < page.rect.width - 14, (name, idx, lo, hi)
            pages.append({"page":idx+1,"leftmost_word_pt":round(lo,1),"rightmost_word_pt":round(hi,1)})
            if args.sheets:
                pix = page.get_pixmap(matrix=fitz.Matrix(.55,.55),alpha=False)
                renders.append(Image.frombytes("RGB", (pix.width,pix.height), pix.samples))
    if args.sheets:
        args.sheets.mkdir(exist_ok=True,parents=True)
        for n in range(0,len(renders),8):
            width,height=renders[n].size
            board=Image.new("RGB",(4*(width+6),2*(height+23)),(232,232,232))
            draw=ImageDraw.Draw(board)
            for pos,im in enumerate(renders[n:n+8]):
                x=(pos%4)*(width+6)
                y=(pos//4)*(height+23)
                board.paste(im,(x,y))
                draw.text((x+8,y+height+2),str(n+pos+1),fill=(20,20,20))
            board.save(args.sheets/f"{name}-{n//8+1}.jpg",quality=83)
    result[path.name]={"sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
                       "pages":len(pages),"word_bounds":pages,"typesetting_warnings":warnings}
    if name == "Symbolic_Complete_Proof":
        assert equation_tags == list(range(1, 160)), "Symbolic equation labels are incomplete or out of order"
        result[path.name]["consecutive_equation_labels"] = [equation_tags[0], equation_tags[-1]]
args.report.write_text(json.dumps(result,indent=2)+"\n")
