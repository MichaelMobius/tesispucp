# Etapa 24 · Barrera cuadrática para Poisson

La fuente normativa es el PDF identificado en el [inventario](INVENTARIO_FORMAL_CAPITULO_III.md), páginas impresas 104–109. La base es la PR #25, commit `c0a86e6ec523dce45bee48e1f81810e408f85ed4`.

| Paso | Declaración Lean | Correspondencia con la tesis |
|---|---|---|
| Operador | `operadorPoisson_eq_laplacianoClásico`, `operadorPoisson_datos` | Parte principal identidad, transporte y orden cero nulos. Signo positivo $\Delta=\partial_{11}+\partial_{22}$. Elipticidad 1. |
| Clausura y barrera | `clausura_cuadrado`, `barreraCuadratica321_suave`, `cotas_barreraCuadratica321`, `barreraCuadratica321_en_cero` | $\overline U=[-1,1]^2$. Se deduce $0\le\psi\le1/2$ de las cotas de coordenadas y el máximo se alcanza en el origen. |
| Derivadas | `parcial_barreraCuadratica321`, `segunda_parcial_barreraCuadratica321`, `laplaciano_barreraCuadratica321` | $D_i\psi=-x_i/2$, $D_{ij}\psi=-\delta_{ij}/2$, $\Delta\psi=-1$. |
| (3.76) puntual | `proposicion321_barrera_cuadratica` | Se reutiliza `estabilidad_de_barrera` con $C_0=1/2$. La prueba controla los dos signos mediante el máximo débil. La acotación del residuo garantiza que los supremos sean reales. |
| (3.76) esencial | `proposicion321_barrera_cuadratica_Linfty`, `proposicion321_Linfty_extendido` | En $U$ se usa volumen restringido. Sobre la frontera, una medida de soporte topológico $\partial U$ da el mismo valor que el supremo puntual. En el enunciado extendido se admite un residuo de norma infinita. |
| Aplicación | `error_poisson321`, `error_poisson321_dirichlet_exacto`, `tasa_error_poisson321_dirichlet_exacto` | La solución y el candidato tienen regularidad clásica. $\Delta(h-u^*)=\Delta h-f$ en $U$ y $h-u^*=h-g$ en $\partial U$. La imposición exacta de Dirichlet elimina el término de borde. |

La constante se obtiene de la barrera y se fija para toda función admisible. El paso del supremo interior al de la clausura usa densidad y continuidad. Para el supremo esencial de frontera se requiere soporte completo, propiedad que `soporte_de_DatosMasa38` deduce en la instancia de muestreo sobre $\partial U$. La medida de volumen restringida al interior y la ley de frontera cumplen funciones distintas.

El corolario de tasas transfiere la cota uniforme del residuo, trayectoria por trayectoria, con constante $1/2$. En un problema de Poisson que satisfaga las premisas de T3.8, puede aplicarse al control interior de (3.28) si la clase impone Dirichlet exacto y la solución es clásica. El Teorema 3.18 ya obtiene el mismo exponente cuando hay un defecto de frontera controlado, con una constante elíptica general. Las Proposiciones 3.11 y 3.15 proporcionan tasas de pérdida cuadrática, que requieren el puente espectral de P3.22 para obtener la tasa uniforme anunciada en C3.23.

## Dependencias para P3.22 y C3.23

| Obligación | Herramientas verificadas en las fuentes de las bibliotecas | Trabajo pendiente |
|---|---|---|
| Base seno del intervalo y del cuadrado | Mathlib `fourierBasis` y `mFourierBasis` construyen bases complejas periódicas. `integral_sin_sq` permite normalizar los senos. | Usar extensión impar, cambio de escala y paso a funciones reales para demostrar completitud de los senos. Justificar la completitud tensorial y la normalización con el volumen, que en P3.22 tiene masa total 4. |
| Autovalores de Dirichlet | Derivación trigonométrica de Mathlib, laplaciano clásico y distribucional del proyecto, principio espectral variacional de EllipticPDE. | Construir los modos seno, verificar frontera nula, pertenencia a `H01` y la identidad $-\Delta\phi_{jk}=\pi^2(j^2+k^2)\phi_{jk}/4$. Extender Green a estos modos y demostrar $F_{jk}=\lambda_{jk}e_{jk}$. |
| Parseval y representante continuo | `HilbertBasis.hasSum_repr`, `lp.hasSum_norm`, `tendstoUniformlyOn_tsum` y las cotas de Cauchy–Schwarz. | Aplicar Parseval a la base seno. Demostrar sumabilidad de $|F_{jk}|/\lambda_{jk}$, usarla como mayorante uniforme y comprobar que el límite coincide con el error en $L^2(U)$. |
| Cota $0.26404$ de (3.77) | `hasSum_zeta_two` para la cota inicial $1/3$, `AntitoneOn.tsum_le_integral` y `Real.pi_gt_d6`. | Reindexar por $\max(j,k)$ para obtener la cola $1/N^2$. Para $N=100$, certificar $S_{100}<0.424317$ con sumas enteras de redondeos superiores de cada término a un denominador común, por ejemplo $10^{12}$. Luego verificar la desigualdad racional para $4\sqrt{0.424417}/\pi^2$. |
| Poincaré óptima y tasas simultáneas | EllipticPDE `dirichlet_poincare_sharp`, `dirichlet_principal_eigenpair_of_bounded` y el Lema 3.19 del proyecto. | Identificar el primer autovalor con $\pi^2/2$ mediante los modos y demostrar que el primer modo alcanza la cota. Aplicar $C_P=\sqrt2/\pi$ y P3.22 al mismo residuo, y transferir la tasa logarítmica de P3.15. |

La próxima prioridad es la base seno y su conexión con el operador distribucional. En paralelo, Taylor y Hermite siguen en el grafo de comparadores. Taylor requiere cotas de coeficientes y resto diferenciado tensorial. Hermite requiere multiplicidades, colisiones, selección boreliana y resto uniforme. Ambas rutas alimentan C3.12 y la certificación de clases neuronales de P3.11/P3.15.
