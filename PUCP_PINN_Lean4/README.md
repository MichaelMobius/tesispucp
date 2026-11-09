# PUCP PINN Lean 4 — Capítulo III

Formalización progresiva de la tesis de Maestría en Matemáticas Aplicadas de la PUCP. La segunda etapa se concentra en el Lema 3.19; el Teorema 3.20 sigue pendiente.

## Reproducir

Con elan y Git disponibles, desde este directorio:

```text
lake update
lake exe cache get
lake build
```

`lean-toolchain` fija Lean 4.35.0; `lakefile.toml` fija Mathlib v4.35.0 y el commit `c47acceaf985f59e1cf3257ffea077a73ea99dae` de [EllipticPDE](https://github.com/alejandro-soto-franco/EllipticPDE). `lake-manifest.json` registra las revisiones resueltas. Los artefactos `.lake` y `.tooling` no se versionan.

## Módulos

- `TesisPINN/Minimalidad.lean`: dos pasos algebraicos condicionales del Teorema 3.8.
- `TesisPINN/Energia.lean`: núcleo hilbertiano previo de la estimación energética; no se cambió en esta etapa.
- `TesisPINN/EnergiaSobolev.lean`: error en `H1Graph.H01`; Poincaré con constante positiva; norma H¹; gradiente distribucional; Green por densidad de funciones de prueba; estimación energética bajo la identidad laplaciana en pruebas.
- `TesisPINN/RedCuadratica.lean`: tres identidades algebraicas del Lema 3.24.

La identificación de la premisa literal `Δe ∈ L²` con la condición `HasTestLaplacian` aún requiere el puente de segundas derivadas distribucionales. Por tanto, la versión literal del Lema 3.19 no se declara completa. Véanse `INFORME_COMPILACION.md` y `MAPA_VERIFICACION.md`. `MANIFEST_SHA256.json` corresponde al ZIP de entrada, no a esta revisión.

