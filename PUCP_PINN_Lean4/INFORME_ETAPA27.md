# Etapa 27 · Estimaciones simultáneas y condición de Dirichlet

Base: [PR #28](https://github.com/MichaelMobius/tesispucp/pull/28), commit `aa07a52090171dfc4fe650362065086b1eb5fffb`. Se cotejaron las páginas impresas 109–110 del PDF normativo identificado en el inventario. En (3.80)–(3.83) se usa $U=(-1,1)^2$, $e=h-u^*$, $\Delta u^*=f$ y $\Delta e=\Delta h-f$. El enunciado determinista pide igual traza Sobolev para cualesquiera $h,u^*\in H^1(U)$, sin requerir representantes continuos de ambos.

## Condición de Dirichlet

`continuo_cero_frontera_mem_H01` demuestra que un grafo de `W12` con representante continuo en la clausura y nulo en la frontera pertenece a `H01`. Para cada nivel $k>0$, el conjunto $\{v\ge k\}$ en la clausura es un compacto contenido en el abierto. La parte positiva $(v-k)^+$ y el gradiente débil truncado son cero fuera de ese compacto. Se aplica la regla de la cadena, se extiende el par por cero y se usa la aproximación por molificación de `H1Graph.mem_H01_of_hasCompactSupport` de EllipticPDE. Se aplica la misma construcción a $-v$. Al tender $k$ a cero, ambas coordenadas del grafo convergen en $L^2$ por convergencia dominada. Para el gradiente se usa que se anula casi en todas partes en $\{v=0\}$.

`frontera_puntual_igual_implica_error_H01` aplica este argumento a la diferencia de dos representantes continuos. Vale para candidatos clásicos y para una solución que solo tenga regularidad $H^1\cap C^0(\overline U)$. `grafoSuaveCuadrado_error_mem_H01` explicita el caso suave global sin exigir factorización del error por $\psi$.

La búsqueda en las versiones fijadas encontró los lemas de truncación, extensión por cero con soporte compacto y molificación. La aproximación global de EllipticPDE requiere `HasC1Boundary`, que no se aplica al cuadrado en sus vértices. Sigue pendiente construir un operador de traza para todo $H^1(U)$ del cuadrado y demostrar $\ker(\operatorname{Tr})=H_0^1(U)$. En particular, la prueba de anulación puntual no descarga por sí misma la formulación literal para dos clases arbitrarias con igual traza. Para la ruta por caras se necesitarían la traza unidimensional casi en cada fibra, su acotación en la medida de cada cara y una prueba de extensión por cero para el núcleo.

## Correspondencia

| Resultado del PDF | Declaración Lean y alcance |
|---|---|
| (3.80), constante óptima de Poincaré | `poincare_cuadrado_espectral` y `poincare_cuadrado_constante_minima`, verificados en la etapa 26. |
| (3.81)–(3.82), cotas simultáneas | `cotas_simultaneas323` toma un error en $H_0^1$ y su laplaciano distribucional $r\in L^2$. Suma las dos cotas con constante explícita $\frac{\sqrt 2}{\pi}\sqrt{1+2/\pi^2}+0.26404$ y obtiene un representante continuo a partir de P3.22. |
| Error entre candidatos y solución | `laplaciano_diferencia323` obtiene $\Delta(h-u^*)=\Delta h-f$. `cotas_simultaneas323_frontera_puntual` descarga $H_0^1$ cuando los representantes continuos coinciden en la frontera. |
| Norma uniforme del error | `representante323_coincide` identifica el representante espectral con la diferencia puntual en la clausura. La igualdad casi en todas partes da igualdad en el abierto porque Lebesgue tiene soporte completo allí. La continuidad lleva la igualdad a la frontera. |
| Normalización de P3.15 | `norma_residuo323_de_perdida` reutiliza $E=\frac14\|r\|_2^2$ y deduce $\|r\|_2=2\sqrt E$. La versión escalar usa la misma ley de muestreo y un representante del residuo en Lebesgue restringida. |
| (3.83), tasa simultánea | `transferencia_simultanea323` pasa de la tasa de pérdida con exponente $1/2$ a la tasa de ambas normas con exponente $1/4$ y prueba la convergencia a cero. `corolario323_escalar` obtiene la tasa de pérdida de P3.15 para los mismos prefijos y las mismas selecciones. |
| (3.83), fronteras exactas | `corolario323_frontera_puntual` da la tasa y ambas convergencias para clases abstractas con representantes continuos de valores iguales sobre toda la frontera, incluidas las clases $C^{2,\alpha}$ de P3.15 cuando se suministran sus grafos y se identifica su operador. `corolario323_poisson_levantado` instancia $G+\psi q$. `corolario323_poisson_levantado_frontera` obtiene la premisa afín de la solución a partir de la igualdad puntual. |

La tasa se expresa mediante `∀ᵐ` y se deduce en el evento casi seguro de P3.15. Se conservan las premisas de `Selecciones315` sobre comparadores, tolerancias y selecciones mensurables. La demostración no construye esos objetos para una arquitectura neuronal. La norma esencial real se usa en las cotas después de garantizar su finitud mediante P3.22.

## Reproducción y continuidad

Ejecutar `lake build` con Lean 4.35.0, Mathlib v4.35.0 y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`. `TrazaCuadrado.lean` y `Corolario323.lean` incluyen las comprobaciones `#check` y `#print axioms`.

La compilación local completó 3307 trabajos. La auditoría de las declaraciones principales devuelve `propext`, `Classical.choice` y `Quot.sound`.

El inventario conserva como obligación el núcleo de la traza Sobolev general. En el bloque de construcciones neuronales, L3.24 debe convertir las identidades cuadráticas existentes en una arquitectura común con sus cotas. P3.25 requiere la interpolación de Hermite y su control uniforme y boreliano. C3.26 depende de esos comparadores para construir las selecciones de mínimos. La transferencia de esta etapa queda disponible para esas instancias.
