"""Manifest CSV SHA256 de archivos realmente depositados.
python reproducibilidad/verificar_deposito.py --crear
python reproducibilidad/verificar_deposito.py
El manifiesto no se incluye a sí mismo. No certifica la ejecución de entrenamientos.
"""
from pathlib import Path
import argparse,csv,hashlib,sys
root=Path(__file__).resolve().parents[1]
manifest=root/'MANIFIESTO_DEPOSITO_SHA256.csv'
exclude={manifest.name}
excluded_suffixes={'.aux','.log','.toc','.out','.blg','.fls','.fdb_latexmk','.synctex.gz','.lof','.lot','.acn','.glo','.gls','.glg'}
excluded_dirs={'.git','__pycache__','.pytest_cache','_build'}

def files():
 for p in sorted(root.rglob('*')):
  if not p.is_file() or p.name in exclude or any(x in excluded_dirs for x in p.relative_to(root).parts) or p.suffix in excluded_suffixes:
   continue
  if p.name in {'main.pdf','texput.pdf'}: continue
  yield p

def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()

ap=argparse.ArgumentParser();ap.add_argument('--crear',action='store_true');args=ap.parse_args()
if args.crear:
 with manifest.open('w',encoding='utf-8',newline='') as f:
  w=csv.writer(f);w.writerow(['ruta_relativa','bytes','sha256'])
  for p in files():w.writerow([p.relative_to(root).as_posix(),p.stat().st_size,sha(p)])
 print('Manifest generado',manifest)
else:
 with manifest.open(encoding='utf-8',newline='') as f:
  rows=list(csv.DictReader(f))
 by_path={x['ruta_relativa']:x for x in rows}
 actual={p.relative_to(root).as_posix():p for p in files()}
 errors=[]
 for rel,r in by_path.items():
  if rel not in actual:errors.append(('faltante',rel));continue
  p=actual[rel]
  if p.stat().st_size!=int(r['bytes']) or sha(p)!=r['sha256']:errors.append(('diferencia',rel))
 for rel in actual.keys()-by_path.keys():errors.append(('inesperado',rel))
 if errors:
  for kind,rel in errors[:25]:print(kind,rel)
  raise SystemExit(f'MANIFIESTO NO VÁLIDO: {len(errors)} problemas')
 print(f'MANIFIESTO VÁLIDO: {len(rows)} archivos, 0 discrepancias, 0 faltantes, 0 archivos inesperados.')
