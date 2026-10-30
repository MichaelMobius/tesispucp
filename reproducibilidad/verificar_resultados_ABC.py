"""Verifica el CSV individual de Colab frente al agregado y las fuentes A.
No reentrena redes ni certifica cotas continuas.
Ejecutar: python reproducibilidad/verificar_resultados_ABC.py
"""
from pathlib import Path
import pandas as pd, numpy as np, hashlib
root=Path(__file__).resolve().parents[1]
r=root/'resultados'
df=pd.read_csv(r/'tanh_ABC_ejecuciones_originales_20261030.csv')
ag=pd.read_csv(r/'tanh_ABC_resumen_reportado_20261030.csv')
org=pd.read_csv(r/'tanh_ABC_resumen_original_Colab_20261030.csv')
assert set(df['protocolo']) == {'A','B','C'}
assert len(df)==16 and df.groupby(['protocolo','ancho']).size().eq(2).all()
assert df[df.protocolo=='C'].query('ancho == 64').sort_values('semilla').eps_final.to_numpy().tolist()==df[df.protocolo=='B'].query('ancho == 64').sort_values('semilla').eps_final.to_numpy().tolist(), 'C debe reutilizar exactamente B W64'
fields={
 'mediana_eps':'eps_final','minimo_eps':'eps_final','maximo_eps':'eps_final',
 'mediana_ratio':'razon_eps_a','mediana_eps_test':'eps_test','mediana_holder':'holder_residuo',
 'mediana_holder_denso':'holder_residuo_denso','mediana_H1_integral':'H1_integral_aprox'
}
errors=[]
for _,a in ag.iterrows():
 rows=df[(df.protocolo==a.protocolo)&(df.ancho==a.ancho)]
 if len(rows)!=int(a.n_semillas): errors.append((a.protocolo,a.ancho,'n_semillas'));continue
 for key,source in fields.items():
  stat='min' if key=='minimo_eps' else 'max' if key=='maximo_eps' else 'median'
  val=float(getattr(rows[source],stat)())
  if not np.isclose(val,float(a[key]),rtol=2e-5,atol=5e-6):
   errors.append((a.protocolo,a.ancho,key,float(a[key]),val))
# direct compare original summary exported from Colab with per-run recalculation, columns shared
for _,a in org.iterrows():
 rows=df[(df.protocolo==a.protocolo)&(df.ancho==a.ancho)]
 if len(rows)!=int(a.n_semillas):errors.append((a.protocolo,a.ancho,'summary_n'));continue
 for col,src in fields.items():
  if col in org.columns:
   method='min' if col=='minimo_eps' else 'max' if col=='maximo_eps' else 'median'
   val=float(getattr(rows[src],method)())
   if not np.isclose(val,float(a[col]),rtol=2e-5,atol=5e-6): errors.append((a.protocolo,a.ancho,'original_'+col))
for record in df[df.protocolo=='A'].itertuples():
 file=root/'reproducibilidad'/'checkpoints_origen_A'/Path(record.origen_checkpoint).name
 if not file.exists():errors.append(('A',record.ancho,'checkpoint_missing',file.name)); continue
 actual=hashlib.sha256(file.read_bytes()).hexdigest()
 if actual!=record.sha256_fuente:errors.append(('A',record.ancho,'checkpoint_sha',file.name))
if errors:
 for err in errors: print('ERROR',err)
 raise SystemExit('FALLÓ la comprobación: '+str(len(errors))+' discrepancias')
print('VERIFICACIÓN EXITOSA: 16 ejecuciones, 8 configuraciones agregadas y 4 fuentes A con SHA-256 coincidente.')
C=df[df.protocolo=='C'].groupby('m_r',as_index=False).eps_final.median()
k=np.polyfit(np.log(C.m_r),np.log(C.eps_final),1)[0]
print(f'Pendiente descriptiva C: {k:.6f} (NO es tasa asintótica certificada)')
