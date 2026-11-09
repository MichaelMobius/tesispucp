# Mapa verificable: tesis, Lean y dependencias

Fuente: tesis PDF de 288 páginas adjunta por el autor. Los números de página indicados como «PDF» son los del visor; la paginación impresa es 13 menor en las páginas aquí citadas.

| Resultado de la tesis | Enunciado y dependencia principal | Código Lean compilado | Estado del resultado completo |
|---|---|---|---|
| Teorema 3.8 (PDF 79-80) | Hipótesis 3.2 y 3.7; muestreo i.i.d., comparadores, minimizadores mensurables, pesos y tasas casi seguras | `Minimalidad.lean`: `regularidad_controlada`, `perdida_empirica_controlada` | Pendiente. Solo pasos de minimalidad condicionales compilados |
| Lema 3.19, (3.71) (PDF 111-113) | `e ∈ H₀¹`, `Δe ∈ L²`, Green débil, Cauchy–Schwarz, Poincaré y norma H¹ | `Energia.lean`: seis declaraciones hasta `energia_norma_par_debil` | Pendiente. Pasos algebraicos e hilbertianos compilados; `hWeak`, `hPoincare` y la identificación Sobolev aún son premisas |
| Teorema 3.20 (PDF 113-115) | Lema 3.19 más trazas iguales, Teorema 3.8, cota inferior de densidad y peso residual positivo | Reutiliza únicamente el núcleo de `Energia.lean` | Pendiente. No están formalizadas la cota (3.74) para funciones ni la convergencia/tasa (3.72)-(3.73) |
| Lema 3.24 (PDF 126-129) | MLP de activación cuadrática con capas ocultas fijas y salida variable; ancho/profundidad acotados | `RedCuadratica.lean`: tres identidades | Pendiente. Falta la arquitectura y su construcción uniforme |
| Teorema 3.4 | Cobertura de Voronoi y generalización | — | Pendiente |
| Proposición 3.15 | Cobertura logarítmica | — | Pendiente |
| Teorema 3.18 | Convergencia uniforme | — | Pendiente |
| Proposición 3.25 / Corolario 3.26 | Comparadores polinómicos y minimizadores | — | Pendiente |

Las once declaraciones Lean enumeradas en `INFORME_COMPILACION.md` compilan con Lean 4.35.0/Mathlib v4.35.0. «Compilado» certifica exactamente la proposición Lean con sus hipótesis escritas, no el enunciado más amplio de la tesis. Todas las once consultas `#print axioms` devolvieron solo `propext`, `Classical.choice` y `Quot.sound`.
