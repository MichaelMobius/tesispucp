# Informe de compilación — segunda etapa (8 de noviembre de 2026)

## Configuración fijada

- Lean: `leanprover/lean4:v4.35.0` (`lean-toolchain`).
- Mathlib: etiqueta `v4.35.0`, commit del manifiesto `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- EllipticPDE de Soto Franco y Marshall-Stevens: commit exacto `c47acceaf985f59e1cf3257ffea077a73ea99dae`, subdirectorio `lean`, paquete Lake `EllipticPdes`. El commit se registró tanto en `lakefile.toml` como en `lake-manifest.json`.
- Se inspeccionaron `EllipticPdes/Sobolev/Graph.lean` y `EllipticPdes/Poincare/GraphBounded.lean`, además de `Sobolev/WeakDeriv.lean` para la semántica distribucional.

## Comandos y resultado

- `lake update`: éxito, código 0; fijó el commit de EllipticPDE sin cambiar el commit de Mathlib.
- `lake build`: éxito, código 0, **3165 trabajos** en la primera compilación conjunta, incluidas `EllipticPdes.Sobolev.Graph`, `EllipticPdes.Poincare.GraphBounded` y `TesisPINN.EnergiaSobolev`.
- Tras ampliar el módulo con Green por densidad y la identificación del gradiente distribucional, `lake build TesisPINN.EnergiaSobolev`: éxito, código 0, 3161 trabajos. La compilación final del objetivo raíz con `lake build` también tuvo éxito, código 0, **3165 trabajos**.
- `#print axioms` para los cinco teoremas nuevos: solo `[propext, Classical.choice, Quot.sound]`; ninguno contiene `sorryAx`.
- No se modificó `TesisPINN/Energia.lean`; SHA256: `DDC5D2DD1A4F3F7E263B4F1CF3E847DFBE039DDAA0AD80A34C06350E6D3CA987`.

Las advertencias de compilación son del sistema de módulos de Mathlib, variables de sección no usadas en tres teoremas nuevos y la variable `he` heredada de `Energia.lean`. No hay errores de compilación en los objetivos indicados.

## Alcance matemático

`EnergiaSobolev.lean` demuestra Poincaré con constante positiva, la identidad cuadrática de la norma H¹ del grafo, que `gradL` es gradiente distribucional cuando el dominio es abierto, Green para el propio error por densidad, y la cota energética bajo la identidad distribucional sobre funciones de prueba `HasTestLaplacian`.

**Pendiente del Lema 3.19 literal:** demostrar que la premisa de la tesis `Δe ∈ L²` y la igualdad distribucional correspondiente implican `HasTestLaplacian`. Falta un lema de laplaciano distribucional en dominio abierto que sume segundas derivadas, use `HasWeakFDerivOn` y convierta la integral de prueba al producto interno `L²`. Esta premisa no se postuló como axioma y no debe confundirse con la hipótesis abstracta `hWeak` entre el error y sí mismo: la nueva identidad se exige solo sobre funciones de prueba y Green para el error se demuestra por continuidad.

**Teorema 3.20:** sigue pendiente. Su parte de trazas, pérdida de PINN, probabilidad y tasas no se infiere del Lema 3.19. Véase `MAPA_VERIFICACION.md` para cada dependencia.


