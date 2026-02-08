#!/bin/bash
# sol.sh - Reference solution for the Performance Lab
# Optimizes rotate() with cache blocking and smooth() with inlined boundary handling

cat > kernels.c << 'SOLEOF'
/********************************************************
 * Kernels to be optimized for the CS:APP Performance Lab
 ********************************************************/

#include <stdio.h>
#include <stdlib.h>
#include "defs.h"

team_t team = {
    "solution",           /* Team name */
    "Reference Solution", /* First member full name */
    "sol@example.com",    /* First member email address */
    "",                   /* Second member full name (leave blank if none) */
    ""                    /* Second member email addr (leave blank if none) */
};

/***************
 * ROTATE KERNEL
 ***************/

char naive_rotate_descr[] = "naive_rotate: Naive baseline implementation";
void naive_rotate(int dim, pixel *src, pixel *dst)
{
    int i, j;
    for (i = 0; i < dim; i++)
        for (j = 0; j < dim; j++)
            dst[RIDX(dim-1-j, i, dim)] = src[RIDX(i, j, dim)];
}

/*
 * rotate - Optimized version using cache blocking (tiling).
 * Process the image in BxB blocks to improve spatial locality.
 */
char rotate_descr[] = "rotate: Current working version";
void rotate(int dim, pixel *src, pixel *dst)
{
    int i, j, bi, bj;
    int B = 32;
    for (bi = 0; bi < dim; bi += B) {
        for (bj = 0; bj < dim; bj += B) {
            int imax = bi + B < dim ? bi + B : dim;
            int jmax = bj + B < dim ? bj + B : dim;
            for (i = bi; i < imax; i++) {
                for (j = bj; j < jmax; j++) {
                    dst[RIDX(dim-1-j, i, dim)] = src[RIDX(i, j, dim)];
                }
            }
        }
    }
}

void register_rotate_functions()
{
    add_rotate_function(&naive_rotate, naive_rotate_descr);
    add_rotate_function(&rotate, rotate_descr);
}

/***************
 * SMOOTH KERNEL
 **************/

char naive_smooth_descr[] = "naive_smooth: Naive baseline implementation";
void naive_smooth(int dim, pixel *src, pixel *dst)
{
    int i, j, ii, jj;
    int sr, sg, sb, num;
    pixel current_pixel;

    for (i = 0; i < dim; i++)
        for (j = 0; j < dim; j++) {
            sr = sg = sb = num = 0;
            for (ii = (i-1 > 0 ? i-1 : 0); ii <= (i+1 < dim-1 ? i+1 : dim-1); ii++)
                for (jj = (j-1 > 0 ? j-1 : 0); jj <= (j+1 < dim-1 ? j+1 : dim-1); jj++) {
                    sr += (int) src[RIDX(ii, jj, dim)].red;
                    sg += (int) src[RIDX(ii, jj, dim)].green;
                    sb += (int) src[RIDX(ii, jj, dim)].blue;
                    num++;
                }
            current_pixel.red = (unsigned short)(sr / num);
            current_pixel.green = (unsigned short)(sg / num);
            current_pixel.blue = (unsigned short)(sb / num);
            dst[RIDX(i, j, dim)] = current_pixel;
        }
}

/*
 * smooth - Optimized version with inlined computation and separate
 * handling of corners, edges, and interior pixels to avoid
 * conditionals and function call overhead in the inner loop.
 */
char smooth_descr[] = "smooth: Current working version";
void smooth(int dim, pixel *src, pixel *dst)
{
    int i, j;
    int last = dim - 1;
    int r, g, b;
    pixel *s;

    /* ---- Four corners: average of 4 pixels ---- */

    /* Top-left (0,0) */
    s = src;
    r  = s->red; g  = s->green; b  = s->blue;
    s = src + 1;
    r += s->red; g += s->green; b += s->blue;
    s = src + dim;
    r += s->red; g += s->green; b += s->blue;
    s = src + dim + 1;
    r += s->red; g += s->green; b += s->blue;
    dst[0].red = r / 4; dst[0].green = g / 4; dst[0].blue = b / 4;

    /* Top-right (0, last) */
    s = src + last - 1;
    r  = s->red; g  = s->green; b  = s->blue;
    s = src + last;
    r += s->red; g += s->green; b += s->blue;
    s = src + dim + last - 1;
    r += s->red; g += s->green; b += s->blue;
    s = src + dim + last;
    r += s->red; g += s->green; b += s->blue;
    dst[last].red = r / 4; dst[last].green = g / 4; dst[last].blue = b / 4;

    /* Bottom-left (last, 0) */
    s = src + (last - 1) * dim;
    r  = s->red; g  = s->green; b  = s->blue;
    s = src + (last - 1) * dim + 1;
    r += s->red; g += s->green; b += s->blue;
    s = src + last * dim;
    r += s->red; g += s->green; b += s->blue;
    s = src + last * dim + 1;
    r += s->red; g += s->green; b += s->blue;
    dst[last * dim].red = r / 4;
    dst[last * dim].green = g / 4;
    dst[last * dim].blue = b / 4;

    /* Bottom-right (last, last) */
    s = src + (last - 1) * dim + last - 1;
    r  = s->red; g  = s->green; b  = s->blue;
    s = src + (last - 1) * dim + last;
    r += s->red; g += s->green; b += s->blue;
    s = src + last * dim + last - 1;
    r += s->red; g += s->green; b += s->blue;
    s = src + last * dim + last;
    r += s->red; g += s->green; b += s->blue;
    dst[last * dim + last].red = r / 4;
    dst[last * dim + last].green = g / 4;
    dst[last * dim + last].blue = b / 4;

    /* ---- Four edges: average of 6 pixels ---- */

    /* Top edge (i=0, j=1..last-1) */
    for (j = 1; j < last; j++) {
        r = g = b = 0;
        s = src + j - 1;       r += s->red; g += s->green; b += s->blue;
        s = src + j;           r += s->red; g += s->green; b += s->blue;
        s = src + j + 1;       r += s->red; g += s->green; b += s->blue;
        s = src + dim + j - 1; r += s->red; g += s->green; b += s->blue;
        s = src + dim + j;     r += s->red; g += s->green; b += s->blue;
        s = src + dim + j + 1; r += s->red; g += s->green; b += s->blue;
        dst[j].red = r / 6; dst[j].green = g / 6; dst[j].blue = b / 6;
    }

    /* Bottom edge (i=last, j=1..last-1) */
    for (j = 1; j < last; j++) {
        int idx = last * dim + j;
        r = g = b = 0;
        s = src + (last - 1) * dim + j - 1; r += s->red; g += s->green; b += s->blue;
        s = src + (last - 1) * dim + j;     r += s->red; g += s->green; b += s->blue;
        s = src + (last - 1) * dim + j + 1; r += s->red; g += s->green; b += s->blue;
        s = src + last * dim + j - 1;       r += s->red; g += s->green; b += s->blue;
        s = src + last * dim + j;           r += s->red; g += s->green; b += s->blue;
        s = src + last * dim + j + 1;       r += s->red; g += s->green; b += s->blue;
        dst[idx].red = r / 6; dst[idx].green = g / 6; dst[idx].blue = b / 6;
    }

    /* Left edge (i=1..last-1, j=0) */
    for (i = 1; i < last; i++) {
        int idx = i * dim;
        r = g = b = 0;
        s = src + (i - 1) * dim;     r += s->red; g += s->green; b += s->blue;
        s = src + (i - 1) * dim + 1; r += s->red; g += s->green; b += s->blue;
        s = src + i * dim;           r += s->red; g += s->green; b += s->blue;
        s = src + i * dim + 1;       r += s->red; g += s->green; b += s->blue;
        s = src + (i + 1) * dim;     r += s->red; g += s->green; b += s->blue;
        s = src + (i + 1) * dim + 1; r += s->red; g += s->green; b += s->blue;
        dst[idx].red = r / 6; dst[idx].green = g / 6; dst[idx].blue = b / 6;
    }

    /* Right edge (i=1..last-1, j=last) */
    for (i = 1; i < last; i++) {
        int idx = i * dim + last;
        r = g = b = 0;
        s = src + (i - 1) * dim + last - 1; r += s->red; g += s->green; b += s->blue;
        s = src + (i - 1) * dim + last;     r += s->red; g += s->green; b += s->blue;
        s = src + i * dim + last - 1;       r += s->red; g += s->green; b += s->blue;
        s = src + i * dim + last;           r += s->red; g += s->green; b += s->blue;
        s = src + (i + 1) * dim + last - 1; r += s->red; g += s->green; b += s->blue;
        s = src + (i + 1) * dim + last;     r += s->red; g += s->green; b += s->blue;
        dst[idx].red = r / 6; dst[idx].green = g / 6; dst[idx].blue = b / 6;
    }

    /* ---- Interior pixels: average of 9 pixels ---- */
    for (i = 1; i < last; i++) {
        for (j = 1; j < last; j++) {
            int idx = i * dim + j;
            r = g = b = 0;
            s = src + (i - 1) * dim + j - 1; r += s->red; g += s->green; b += s->blue;
            s = src + (i - 1) * dim + j;     r += s->red; g += s->green; b += s->blue;
            s = src + (i - 1) * dim + j + 1; r += s->red; g += s->green; b += s->blue;
            s = src + i * dim + j - 1;       r += s->red; g += s->green; b += s->blue;
            s = src + i * dim + j;           r += s->red; g += s->green; b += s->blue;
            s = src + i * dim + j + 1;       r += s->red; g += s->green; b += s->blue;
            s = src + (i + 1) * dim + j - 1; r += s->red; g += s->green; b += s->blue;
            s = src + (i + 1) * dim + j;     r += s->red; g += s->green; b += s->blue;
            s = src + (i + 1) * dim + j + 1; r += s->red; g += s->green; b += s->blue;
            dst[idx].red = r / 9; dst[idx].green = g / 9; dst[idx].blue = b / 9;
        }
    }
}

void register_smooth_functions()
{
    add_smooth_function(&smooth, smooth_descr);
    add_smooth_function(&naive_smooth, naive_smooth_descr);
}
SOLEOF

chmod +x kernels.c
