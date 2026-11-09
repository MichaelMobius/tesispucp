# PUCP PINN Lean 4 — Capítulo III

Formalización progresiva de la tesis de Maestría en Matemáticas Aplicadas de la PUCP. En la tercera etapa quedó compilada la estimación analítica del Lema 3.19 en `ℝ²`, con el laplaciano definido como distribución sobre un abierto. El Teorema 3.20 sigue pendiente.

## Reproducir

Con elan y Git disponibles, desde este directorio:

```text
lake update
lake exe cache get
lake build
```

`lean-toolchain` fija Lean 4.35.0; `lakefile.toml` fija Mathlib v4.35.0 y EllipticPDE en `c47acceaf985f59e1cf3257ffea077a73ea99dae`. `lake-manifest.json` registra las revisiones resueltas. `.lake` y `.tooling` no se versionan.

## Módulos

- `TesisPINN/Minimalidad.lean`: dos pasos algebraicos condicionales del Teorema 3.8.
- `TesisPINN/Energia.lean`: núcleo hilbertiano de la estimación energética.
- `TesisPINN/EnergiaSobolev.lean`: Poincaré, norma H¹ y Green por densidad para `H1Graph.H01`.
- `TesisPINN/LaplacianoDistribucional.lean`: laplaciano de `𝓓′(Ω)` en `ℝ²`, derivadas de funciones de prueba, puente hacia `HasTestLaplacian` y estimación final con medida de Lebesgue.
- `TesisPINN/RedCuadratica.lean`: tres identidades algebraicas del Lema 3.24.

La estimación final supone `U ∈ H₀¹` representado por el cierre de grafos de prueba, `Ω` abierto acotado y `ΔU=r∈L²` como igualdad de distribuciones. La conexión de las trazas y los residuos de las soluciones PINN concretas con este enunciado, así como las tasas probabilísticas, pertenecen al Teorema 3.20 y siguen pendientes. Véanse `INFORME_COMPILACION.md` y `MAPA_VERIFICACION.md`. `MANIFEST_SHA256.json` corresponde al ZIP de entrada.

