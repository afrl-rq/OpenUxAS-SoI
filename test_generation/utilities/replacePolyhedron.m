function [ new_V ] = replacePolyhedron( poly_V, area_x_min, area_x_max, area_y_min, area_y_max, path_cell )
%replacePolyhedron Randomly places the given polyhedron in yhe given area 
%without overlapping with the points in given paths.

intersects = true;
displace_count = 0;
if ~isempty(path_cell)
    while intersects && displace_count < 5*size(path_cell{1}, 1)*length(path_cell)
        x_disp = (area_x_max - area_x_min)*rand(1,1) + area_x_min;
        y_disp = (area_y_max - area_y_min)*rand(1,1) + area_y_min;

        new_V = poly_V;
        offset = new_V(1, :); % We will use it to first move the first corner of the polyhedron to the origin. (-offset below)
        for i = 1:size(new_V, 1)
            new_V(i, 1) = new_V(i, 1) + x_disp - offset(1);
            new_V(i, 2) = new_V(i, 2) + y_disp - offset(2);
        end

        displace_count_inner = 0;
        while intersects && displace_count_inner < (size(path_cell{1}, 1)*length(path_cell) / 2)
            intersects = false;
            for p = 1:length(path_cell)
                pt_array = path_cell{p};
                pt_array = [pt_array(:,2), pt_array(:,1)];
                for i = 1:size(pt_array, 1)
                    if is_pt_in_poly(new_V, pt_array(i, :))
                        [ shortest_dist, closest_pt ] = distance_from_pt_to_polygon(new_V, pt_array(i, :));
                        shoot_vector = closest_pt - pt_array(i, :);
                        if norm(shoot_vector) > 0.0
                            shoot_vector = shoot_vector./norm(shoot_vector);
                            disp_vector = -1.25*shortest_dist.*shoot_vector; % Move away from the closest point in polygon
                            for j = 1:size(new_V, 1)
                                new_V(j, :) = new_V(j, :) + disp_vector;
                            end
                            displace_count_inner = displace_count_inner + 1;
                            displace_count = displace_count + 1;
                            intersects = true;
                        end
                    else
                        if intersects %Previous point intersected but this one does not.
                            break;
                        end
                    end
                end
            end
        end
    end
    if intersects
        disp 'Gave up replacing poly!'
        new_V = [];
    end
    displace_count
    %plot_path_and_polygon(pt_arr, new_P)
else
    new_V = poly_V;
end
end

