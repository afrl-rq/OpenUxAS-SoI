function [ is_inside ] = is_pt_in_poly( poly_vertices, pt )
%is_pt_in_poly Checks if point is in the polygon which is given by the
%vertice coordinates.
% Algorithm:
% Point Inclusion in Polygon Test
% W. Randolph Franklin (WRF)
% Code adopted from:
% https://wrf.ecse.rpi.edu//Research/Short_Notes/pnpoly.html

is_inside = false;
num_vertices = size(poly_vertices, 1);
j = num_vertices;
for i = 1:num_vertices
    if (((poly_vertices(i, 2) > pt(2)) ~= (poly_vertices(j, 2) > pt(2))) && ...
            (pt(1) < (poly_vertices(j, 1) - poly_vertices(i, 1)) * (pt(2) - poly_vertices(i, 2)) ...
            / (poly_vertices(j, 2) - poly_vertices(i,2)) + poly_vertices(i, 1)) )
       is_inside = ~is_inside;
    end
    j = i;
end
end
