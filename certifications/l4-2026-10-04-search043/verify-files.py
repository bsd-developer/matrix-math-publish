#!/usr/bin/env python3
"""Verify inventory and lossless payload identities, not mathematical acceptance."""
from pathlib import Path
import gzip, hashlib, json

ROOT=Path(__file__).resolve().parent
def hashed(stream):
    h=hashlib.sha256(); count=0
    for b in iter(lambda:stream.read(1024*1024),b''):
        h.update(b);count+=len(b)
    return h.hexdigest(),count

def main():
    m=json.loads((ROOT/'manifest.json').read_text())
    if m['schema']!='search043-public-file-inventory/1': raise ValueError('Unknown inventory schema')
    seen=set()
    for r in m['files']:
        p=Path(r['path'])
        if p.is_absolute() or '..' in p.parts or r['path'] in seen: raise ValueError('Unsafe or duplicate path')
        seen.add(r['path']); actual=ROOT/p
        if actual.is_symlink() or not actual.resolve().is_relative_to(ROOT): raise ValueError('Nonlocal file')
        with actual.open('rb') as f: sha,size=hashed(f)
        if (sha,size)!=(r['sha256'],r['bytes']): raise ValueError('File mismatch: '+r['path'])
    for line in (ROOT/'SHA256SUMS').read_text().splitlines():
        expected,relative=line.split('  ',1)
        if relative not in seen and relative!='manifest.json': raise ValueError('Unlisted checksum')
        with (ROOT/relative).open('rb') as f: actual,_=hashed(f)
        if actual!=expected: raise ValueError('Checksum mismatch: '+relative)
    g=m['generated_module']
    with gzip.open(ROOT/g['compressed_path'],'rb') as f: sha,size=hashed(f)
    if (sha,size)!=(g['sha256'],g['bytes']): raise ValueError('Decompressed theorem mismatch')
    cert=m['certificate']; row=next(x for x in m['files'] if x['path']==cert['path'])
    if any(row[k]!=cert[k] for k in ['bytes','sha256']): raise ValueError('Certificate identity mismatch')
    print(json.dumps({'passed':True,'scope':'file identities and lossless theorem transport only',
       'files_checked':len(seen),'certificate_sha256':cert['sha256'],'certificate_bytes':cert['bytes'],
       'generated_module_sha256':sha,'generated_module_bytes':size},sort_keys=True))
if __name__=='__main__': main()
