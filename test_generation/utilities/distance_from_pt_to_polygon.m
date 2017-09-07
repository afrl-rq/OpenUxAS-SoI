function [ shortest_dist, closest_pt ] = distance_from_pt_to_polygon( poly_vertices, pt )
%distance_from_pt_to_polygon Finds the distance and closest point on
%polygon to the given point. Negative if inside the polygon.

num_vertices = size(poly_vertices, 1);
j = num_vertices;
closest_pt_arr = poly_vertices;
shortest_dist_arr = zeros(num_vertices, 1);
for i = 1:num_vertices
    seg_a = poly_vertices(j, :);
    seg_b = poly_vertices(i, :);
    segment_length_squared = (seg_a(1) - seg_b(1))^2 + (seg_a(2) - seg_b(2))^2;
    if segment_length_squared > 0.0
        t = max(0, min(1, dot(pt - seg_a, seg_b - seg_a) / segment_length_squared));
        closest_pt_arr(i, :) = seg_a + t * (seg_b - seg_a);
        shortest_dist_arr(i) = norm(pt - closest_pt_arr(i, :));
    else
        closest_pt_arr(i, :) = seg_a;
        shortest_dist_arr(i) = 0;
    end
    j = i;
end
[shortest_dist, i] = min(shortest_dist_arr);
closest_pt = closest_pt_arr(i, :);

end

