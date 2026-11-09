# PUCP PINN Lean 4 — Capítulo III

Proyecto de formalización progresiva de la tesis de Maestría en Matemáticas Aplicadas de la PUCP. **Estado al 8 de noviembre de 2026:** `lake build` exitoso con Lean 4.35.0 y Mathlib v4.35.0; once declaraciones compiladas y auditadas con `#print axioms`. Ningún teorema completo del Capítulo III ha sido certificado todavía.

## Reproducir

Desde este directorio, con elan y Git disponibles:

```text
lake update
lake exe cache get
lake build
```

En esta ejecución de Windows se ubicó temporalmente `ELAN_HOME` en `D:\PUCP_PINN_Lean4\.tooling\elan` por falta de espacio en C:. La carpeta `.tooling` y `.lake` no se versionan. El archivo `lake-manifest.json` fija la revisión exacta de Mathlib.

## Código

- `TesisPINN/Minimalidad.lean`: dos consecuencias algebraicas condicionales de la minimalidad usada en el Teorema 3.8.
- `TesisPINN/Energia.lean`: seis resultados del núcleo de la estimación energética, incluida la deducción de la cota de Green por Cauchy–Schwarz desde una identidad débil entre espacios con producto interno y la cota de la norma del par `(error, gradiente)` con coeficiente `Cₚ√(1+Cₚ²)`.
- `TesisPINN/RedCuadratica.lean`: tres identidades de activación cuadrática y factor de frontera utilizadas en el Lema 3.24.

Las hipótesis `hWeak` y `hPoincare` en `Energia.lean` no son axiomas nuevos: son premisas explícitas de los teoremas condicionales. Aún hay que obtenerlas para el error de Poisson como función de `H₀¹`, y vincular la norma del par con la norma Sobolev `H¹`. La convergencia y la tasa del Teorema 3.20 requieren además formalizar sus hipótesis de muestreo, comparadores, minimizadores y densidad.

Véanse [el informe de compilación](INFORME_COMPILACION.md) y [el mapa tesis–Lean](MAPA_VERIFICACION.md) para la clasificación exacta. `MANIFEST_SHA256.json` documenta la integridad del ZIP original, antes de estas modificaciones.
